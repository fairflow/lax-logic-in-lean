/-
# FRJ(G) — Preliminaries

A faithful formalisation of

  Camillo Fiorentini and Mauro Ferrari,
  *Duality between unprovability and provability in forward proof-search
  for Intuitionistic Propositional Logic*,
  ACM Transactions on Computational Logic 21(3), 2020.
  Source text used: the arXiv LaTeX source of arXiv:1804.06689
  (`frj-corr.tex`), which is the full journal version.

This file is Section 2 (Preliminaries) of that paper, clause by clause.
Every definition below carries the paper's own wording in its docstring;
divergences, where any, are flagged with the word DIVERGENCE and
recorded in `docs/frj-fidelity.md`.

**Scope note.**  The paper defines IPL *semantically*: "Intuitionistic
Propositional Logic IPL coincides with the set of valid formulas".  Both
results in scope (soundness and completeness of FRJ(G)) are therefore
statements about Kripke semantics alone, and no proof system for IPC is
needed anywhere in this development.
-/
import Mathlib

namespace FRJ

/-! ## The language `L`

"We consider the propositional language `L` based on a denumerable set
of propositional variables `PV`, the connectives ∧, ∨, ⊃ and the logical
constant ⊥; ¬A is a shorthand for A ⊃ ⊥."
-/

/-- Formulas of `L`.  Propositional variables are named by strings, which
is the repo's standing convention for a denumerable `PV`. -/
inductive Form where
  | atom : String → Form
  | bot : Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
  deriving DecidableEq, Repr

namespace Form

/-- `¬A` is a shorthand for `A ⊃ ⊥`. -/
def neg (A : Form) : Form := .imp A .bot

/-- The size of `A`: "the number of symbols in `A`". -/
def size : Form → Nat
  | .atom _ => 1
  | .bot => 1
  | .and A B => size A + size B + 1
  | .or A B => size A + size B + 1
  | .imp A B => size A + size B + 1

/-- `A` is a propositional variable, i.e. `A ∈ PV`. -/
def isPV : Form → Bool
  | .atom _ => true
  | _ => false

/-- "By `Prime` we denote the set `PV ++ {⊥}`." -/
def isPrime : Form → Bool
  | .atom _ => true
  | .bot => true
  | _ => false

/-- "By `Fm⊃` [we denote] the set of ⊃-formulas of `L`." -/
def isImp : Form → Bool
  | .imp _ _ => true
  | _ => false

theorem isPV_isPrime {A : Form} (h : A.isPV = true) : A.isPrime = true := by
  cases A <;> simp_all [isPV, isPrime]

end Form

/-! ### Choice-free list utilities

Three Mathlib lemmas this development would otherwise reach for are
`Classical.choice`-tainted: `List.argmax_mem`, `List.le_of_mem_argmax`
and `List.eq_nil_iff_forall_not_mem`.  (`List.argmax` itself is clean;
it is its specification lemmas that are not.)  The replacements are
elementary. -/

/-- A list with no members is empty. -/
theorem eq_nil_of_forall_not_mem {α : Type} : ∀ {l : List α}, (∀ x, x ∉ l) → l = []
  | [], _ => rfl
  | x :: _, h => absurd List.mem_cons_self (h x)

/-- An element of `a :: l` maximising `f`. -/
def maxOn {α : Type} (f : α → Nat) : α → List α → α
  | a, [] => a
  | a, b :: l => if f a < f b then maxOn f b l else maxOn f a l

theorem maxOn_mem {α : Type} (f : α → Nat) :
    ∀ (a : α) (l : List α), maxOn f a l ∈ a :: l
  | a, [] => List.mem_cons_self
  | a, b :: l => by
      by_cases h : f a < f b
      · rw [maxOn, if_pos h]
        rcases List.mem_cons.mp (maxOn_mem f b l) with h' | h'
        · rw [h']; exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
      · rw [maxOn, if_neg h]
        rcases List.mem_cons.mp (maxOn_mem f a l) with h' | h'
        · rw [h']; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')

theorem le_maxOn {α : Type} (f : α → Nat) :
    ∀ (a : α) (l : List α), ∀ x ∈ a :: l, f x ≤ f (maxOn f a l)
  | a, [], x, hx => by
      rcases List.mem_cons.mp hx with rfl | h
      · rw [maxOn]
      · exact absurd h List.not_mem_nil
  | a, b :: l, x, hx => by
      by_cases h : f a < f b
      · rw [maxOn, if_pos h]
        have ih := le_maxOn f b l
        rcases List.mem_cons.mp hx with rfl | h'
        · exact Nat.le_trans (Nat.le_of_lt h) (ih b List.mem_cons_self)
        · exact ih x h'
      · rw [maxOn, if_neg h]
        have ih := le_maxOn f a l
        rcases List.mem_cons.mp hx with rfl | h'
        · exact ih x List.mem_cons_self
        · rcases List.mem_cons.mp h' with rfl | h''
          · exact Nat.le_trans (Nat.not_lt.mp h) (ih a List.mem_cons_self)
          · exact ih x (List.mem_cons_of_mem _ h'')

/-! ## Finite sets as lists

The development uses sets of formulas only up to membership, so lists
serve.  This is not a stylistic choice: Mathlib's `Finset` union, erase
and image are `Classical.choice`-tainted **at the definition level**, so
any term mentioning them carries choice however it is proved.  The `List`
operations below are axiom-free. -/

/-- Set difference by a single element (`Finset.erase`'s replacement). -/
def rm (l : List Form) (x : Form) : List Form := l.filter (fun y => decide (y ≠ x))

@[simp] theorem mem_rm {l : List Form} {x y : Form} :
    y ∈ rm l x ↔ (y ≠ x ∧ y ∈ l) := by
  simp only [rm, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem rm_subset {l : List Form} {x : Form} : rm l x ⊆ l :=
  fun _ h => (mem_rm.mp h).2

theorem notMem_rm {l : List Form} {x : Form} : x ∉ rm l x :=
  fun h => (mem_rm.mp h).1 rfl

/-- Intersection (`Finset.inter`'s replacement). -/
def cap (l m : List Form) : List Form := l.filter (fun y => decide (y ∈ m))

@[simp] theorem mem_cap {l m : List Form} {y : Form} :
    y ∈ cap l m ↔ (y ∈ l ∧ y ∈ m) := by
  simp [cap, List.mem_filter]

theorem cap_subset_cap {Γ m m' : List Form} (h : m ⊆ m') : cap Γ m ⊆ cap Γ m' :=
  fun _ hy => mem_cap.mpr ⟨(mem_cap.mp hy).1, h (mem_cap.mp hy).2⟩

/-- Set difference (`Finset.sdiff`'s replacement). -/
def sdiff (l m : List Form) : List Form := l.filter (fun y => decide (y ∉ m))

@[simp] theorem mem_sdiff {l m : List Form} {y : Form} :
    y ∈ sdiff l m ↔ (y ∈ l ∧ y ∉ m) := by
  simp [sdiff, List.mem_filter]

theorem sdiff_subset {l m : List Form} : sdiff l m ⊆ l :=
  fun _ h => (mem_sdiff.mp h).1

/-- A difference meets what it was taken against in nothing at all —
literally the empty list, which is what the `⊃∈` side condition wants. -/
theorem cap_sdiff_eq_nil {l m : List Form} : cap (sdiff l m) m = [] := by
  refine eq_nil_of_forall_not_mem (fun x hx => ?_)
  obtain ⟨hx1, hx2⟩ := mem_cap.mp hx
  exact (mem_sdiff.mp hx1).2 hx2


/-! ## Kripke models

"A Kripke model is a structure `K = ⟨P, ≤, ρ, V⟩`, where `⟨P,≤⟩` is a
finite poset with minimum `ρ` (the root of `K`) and `V : P → 2^PV` is a
function such that `α ≤ β` implies `V(α) ⊆ V(β)`."

Note what is NOT here: there are no fallible worlds.  `K,α ⊮ ⊥` holds at
every world by definition of forcing.
-/

/-- A Kripke model: a finite poset with a minimum, carrying a monotone
valuation of propositional variables. -/
structure Kripke where
  /-- the set `P` of worlds -/
  W : Type
  /-- "⟨P,≤⟩ is a finite poset", presented constructively: a list of all
  worlds.  (A `Finite` instance would force `Fintype.ofFinite` later,
  which costs `Classical.choice`.) -/
  elems : List W
  complete : ∀ w, w ∈ elems
  decEq : DecidableEq W
  le : W → W → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  /-- the root `ρ`, the minimum of the poset -/
  root : W
  root_le : ∀ a, le root a
  /-- `V : P → 2^PV` -/
  V : W → String → Prop
  /-- "`α ≤ β` implies `V(α) ⊆ V(β)`" -/
  V_mono : ∀ {a b}, le a b → ∀ p, V a p → V b p
  /-- the order and the valuation are decidable: the models the paper
  works with are finite and concrete, and decidability is what keeps the
  development free of `Classical.choice`. -/
  decLe : ∀ a b, Decidable (le a b)
  decV : ∀ a p, Decidable (V a p)

attribute [instance] Kripke.decEq Kripke.decLe Kripke.decV

/-! ### Counting, for the height of a world

`Finset.card` would do this, but `Finset` carries `Classical.choice` at
the definition level.  `List.countP` over the world enumeration does the
same job constructively. -/

theorem countP_mono {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      l.countP p ≤ l.countP q
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
      have ih := countP_mono (fun y hy => h y (List.mem_cons_of_mem _ hy))
      rw [List.countP_cons, List.countP_cons]
      cases hpx : p x with
      | false =>
          rw [if_neg (fun hc => Bool.noConfusion hc)]
          cases hqx : q x with
          | false => rw [if_neg (fun hc => Bool.noConfusion hc)]; omega
          | true => rw [if_pos rfl]; omega
      | true =>
          rw [if_pos rfl, if_pos (h x List.mem_cons_self hpx)]
          omega

/-- Strict version: if in addition some member satisfies `q` but not `p`. -/
theorem countP_lt_countP {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      ∀ {b : α}, b ∈ l → q b = true → p b = false →
      l.countP p < l.countP q
  | [], _, _, hb, _, _ => absurd hb (List.not_mem_nil)
  | x :: xs, h, b, hb, hqb, hpb => by
      have hmono := countP_mono (l := xs)
        (fun y hy => h y (List.mem_cons_of_mem _ hy))
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp hb with rfl | hb'
      · rw [hpb, hqb, if_neg (fun hc => Bool.noConfusion hc), if_pos rfl]
        omega
      · have ih := countP_lt_countP
          (fun y hy => h y (List.mem_cons_of_mem _ hy)) hb' hqb hpb
        cases hpx : p x with
        | false =>
            rw [if_neg (fun hc => Bool.noConfusion hc)]
            cases hqx : q x with
            | false => rw [if_neg (fun hc => Bool.noConfusion hc)]; omega
            | true => rw [if_pos rfl]; omega
        | true =>
            rw [if_pos rfl, if_pos (h x List.mem_cons_self hpx)]
            omega


namespace Kripke

/-- The forcing relation, exactly the five clauses of the paper.

DIVERGENCE (presentational, standard): the paper writes the ⊃-clause as
"for every β ≥ α, `K,β ⊮ A` or `K,β ⊩ B`"; we write the equivalent
implication `∀ β ≥ α, K,β ⊩ A → K,β ⊩ B`, which is the standard reading
and avoids an appeal to excluded middle in the definition itself. -/
def force (K : Kripke) : K.W → Form → Prop
  | _, .bot => False
  | a, .atom p => K.V a p
  | a, .and A B => force K a A ∧ force K a B
  | a, .or A B => force K a A ∨ force K a B
  | a, .imp A B => ∀ b, K.le a b → force K b A → force K b B

variable (K : Kripke)

@[simp] theorem force_bot (a : K.W) : ¬ K.force a .bot := by
  simp [force]

@[simp] theorem force_atom (a : K.W) (p : String) :
    K.force a (.atom p) ↔ K.V a p := by simp [force]

@[simp] theorem force_and (a : K.W) (A B : Form) :
    K.force a (.and A B) ↔ (K.force a A ∧ K.force a B) := by simp [force]

@[simp] theorem force_or (a : K.W) (A B : Form) :
    K.force a (.or A B) ↔ (K.force a A ∨ K.force a B) := by simp [force]

@[simp] theorem force_imp (a : K.W) (A B : Form) :
    K.force a (.imp A B) ↔ ∀ b, K.le a b → K.force b A → K.force b B := by
  simp [force]

/-- "Monotonicity property holds for arbitrary formulas, i.e.
`K,α ⊩ A` and `α ≤ β` imply `K,β ⊩ A`." -/
theorem force_mono {a b : K.W} (hab : K.le a b) :
    ∀ {A : Form}, K.force a A → K.force b A := by
  intro A
  induction A with
  | atom p => exact fun h => K.V_mono hab p h
  | bot => exact fun h => h.elim
  | and A B ihA ihB => exact fun h => ⟨ihA h.1, ihB h.2⟩
  | or A B ihA ihB => exact fun h => h.elim (Or.inl ∘ ihA) (Or.inr ∘ ihB)
  | imp A B _ _ => exact fun h c hbc => h c (K.le_trans hab hbc)

/-! ### Forcing is decidable

The paper's models are finite, and `Kripke` carries the witnesses of that
constructively (`elems`/`complete`, `decLe`, `decV`).  So forcing is a
COMPUTATION, not merely a proposition — which is what lets `Λ*_α` below
be an ordinary `List.filter` rather than a classically-formed subset,
and is the reason this development needs no `Classical.choice`. -/

instance decForce (K : Kripke) : ∀ (a : K.W) (A : Form), Decidable (K.force a A)
  | _, .bot => inferInstanceAs (Decidable False)
  | a, .atom p => K.decV a p
  | a, .and A B =>
      have := decForce K a A
      have := decForce K a B
      inferInstanceAs (Decidable (_ ∧ _))
  | a, .or A B =>
      have := decForce K a A
      have := decForce K a B
      inferInstanceAs (Decidable (_ ∨ _))
  | a, .imp A B =>
      have : ∀ b : K.W, Decidable (K.force b A) := fun b => decForce K b A
      have : ∀ b : K.W, Decidable (K.force b B) := fun b => decForce K b B
      have : Decidable (∀ b ∈ K.elems, K.le a b → K.force b A → K.force b B) :=
        List.decidableBAll _ _
      decidable_of_iff (∀ b ∈ K.elems, K.le a b → K.force b A → K.force b B)
        ⟨fun h b => h b (K.complete b), fun h b _ => h b⟩

/-- "`K,α ⊩ Γ` means `K,α ⊩ A` for every `A ∈ Γ`." -/
def forces (a : K.W) (Γ : List Form) : Prop := ∀ A ∈ Γ, K.force a A

theorem forces_mono {a b : K.W} (hab : K.le a b) {Γ : List Form}
    (h : K.forces a Γ) : K.forces b Γ :=
  fun A hA => K.force_mono hab (h A hA)

/-- "A formula `A` is valid in `K` iff `K,ρ ⊩ A`." -/
def valid (A : Form) : Prop := K.force K.root A

end Kripke

/-- "`A` is valid iff `A` is valid in all the Kripke models;
Intuitionistic Propositional Logic IPL coincides with the set of valid
formulas."  This is the paper's definition of `IPL`, and the only one
this development uses. -/
def IPL (A : Form) : Prop := ∀ K : Kripke, K.valid A

/-- "If `K,ρ ⊮ A`, we say that `K` is a countermodel for `A`." -/
def Countermodel (K : Kripke) (A : Form) : Prop := ¬ K.valid A

theorem not_IPL_of_countermodel {K : Kripke} {A : Form}
    (h : Countermodel K A) : ¬ IPL A := fun hA => h (hA K)

/-! ## Subformulas, and the left/right (negative/positive) split

"Given a formula `G`, `Sf(G)` is the set of all subformulas of `G`
(including `G` itself).  By `Sf^L(G)` and `Sf^R(G)` we denote the subsets
of left and right subformulas of `G`.  Formally, `Sf^L(G)` and `Sf^R(G)`
are the smallest subsets of `Sf(G)` such that:

* `G ∈ Sf^R(G)`;
* `A ⊙ B ∈ Sf^g(G)` implies `{A,B} ⊆ Sf^g(G)`, where `⊙ ∈ {∧,∨}` and
  `Sf^g ∈ {Sf^L, Sf^R}`;
* `A ⊃ B ∈ Sf^L(G)` implies `B ∈ Sf^L(G)` and `A ∈ Sf^R(G)`;
* `A ⊃ B ∈ Sf^R(G)` implies `B ∈ Sf^R(G)` and `A ∈ Sf^L(G)`."

We compute the two sets simultaneously.  `sfPos A` is the pair
`(right-subformulas, left-subformulas)` generated by `A` occurring in
RIGHT position, and `sfNeg A` the pair generated by `A` occurring in LEFT
position.  Then `Sf^R(G) = (sfPos G).1` and `Sf^L(G) = (sfPos G).2`.
-/

open Form in
mutual
  /-- The `(Sf^R, Sf^L)` contribution of a formula occurring in RIGHT position. -/
  def sfPos : Form → List Form × List Form
    | .atom p => ([Form.atom p], [])
    | .bot => ([Form.bot], [])
    | .and A B =>
        ((Form.and A B) :: ((sfPos A).1 ++ (sfPos B).1), (sfPos A).2 ++ (sfPos B).2)
    | .or A B =>
        ((Form.or A B) :: ((sfPos A).1 ++ (sfPos B).1), (sfPos A).2 ++ (sfPos B).2)
    | .imp A B =>
        ((Form.imp A B) :: ((sfNeg A).1 ++ (sfPos B).1), (sfNeg A).2 ++ (sfPos B).2)

  /-- The `(Sf^R, Sf^L)` contribution of a formula occurring in LEFT position. -/
  def sfNeg : Form → List Form × List Form
    | .atom p => ([], [Form.atom p])
    | .bot => ([], [Form.bot])
    | .and A B =>
        ((sfNeg A).1 ++ (sfNeg B).1, (Form.and A B) :: ((sfNeg A).2 ++ (sfNeg B).2))
    | .or A B =>
        ((sfNeg A).1 ++ (sfNeg B).1, (Form.or A B) :: ((sfNeg A).2 ++ (sfNeg B).2))
    | .imp A B =>
        ((sfPos A).1 ++ (sfNeg B).1, (Form.imp A B) :: ((sfPos A).2 ++ (sfNeg B).2))
end

/-- `Sf^R(G)`, the right (positive) subformulas of `G`. -/
def sfR (G : Form) : List Form := (sfPos G).1

/-- `Sf^L(G)`, the left (negative) subformulas of `G`. -/
def sfL (G : Form) : List Form := (sfPos G).2

/-! ### The characterisation, as the paper states it

These four theorems are the fidelity check on `sfR`/`sfL`: they are the
paper's four defining clauses, proved of our computed sets.
-/

/-- The paper's four defining clauses, as a property of a pair of sets
`(R, L)` standing for `(Sf^R(G), Sf^L(G))`. -/
structure SfClosed (R L : List Form) : Prop where
  rAnd : ∀ {A B : Form}, Form.and A B ∈ R → A ∈ R ∧ B ∈ R
  rOr : ∀ {A B : Form}, Form.or A B ∈ R → A ∈ R ∧ B ∈ R
  rImp : ∀ {A B : Form}, Form.imp A B ∈ R → A ∈ L ∧ B ∈ R
  lAnd : ∀ {A B : Form}, Form.and A B ∈ L → A ∈ L ∧ B ∈ L
  lOr : ∀ {A B : Form}, Form.or A B ∈ L → A ∈ L ∧ B ∈ L
  lImp : ∀ {A B : Form}, Form.imp A B ∈ L → A ∈ R ∧ B ∈ L

theorem SfClosed.union {R₁ L₁ R₂ L₂ : List Form}
    (h₁ : SfClosed R₁ L₁) (h₂ : SfClosed R₂ L₂) :
    SfClosed (R₁ ++ R₂) (L₁ ++ L₂) := by
  constructor <;> intro A B hmem <;>
    rcases List.mem_append.mp hmem with h | h
  · exact ⟨List.mem_append_left _ (h₁.rAnd h).1, List.mem_append_left _ (h₁.rAnd h).2⟩
  · exact ⟨List.mem_append_right _ (h₂.rAnd h).1, List.mem_append_right _ (h₂.rAnd h).2⟩
  · exact ⟨List.mem_append_left _ (h₁.rOr h).1, List.mem_append_left _ (h₁.rOr h).2⟩
  · exact ⟨List.mem_append_right _ (h₂.rOr h).1, List.mem_append_right _ (h₂.rOr h).2⟩
  · exact ⟨List.mem_append_left _ (h₁.rImp h).1, List.mem_append_left _ (h₁.rImp h).2⟩
  · exact ⟨List.mem_append_right _ (h₂.rImp h).1, List.mem_append_right _ (h₂.rImp h).2⟩
  · exact ⟨List.mem_append_left _ (h₁.lAnd h).1, List.mem_append_left _ (h₁.lAnd h).2⟩
  · exact ⟨List.mem_append_right _ (h₂.lAnd h).1, List.mem_append_right _ (h₂.lAnd h).2⟩
  · exact ⟨List.mem_append_left _ (h₁.lOr h).1, List.mem_append_left _ (h₁.lOr h).2⟩
  · exact ⟨List.mem_append_right _ (h₂.lOr h).1, List.mem_append_right _ (h₂.lOr h).2⟩
  · exact ⟨List.mem_append_left _ (h₁.lImp h).1, List.mem_append_left _ (h₁.lImp h).2⟩
  · exact ⟨List.mem_append_right _ (h₂.lImp h).1, List.mem_append_right _ (h₂.lImp h).2⟩

/-- Inserting a compound formula into the RIGHT component preserves the
clauses, provided its own components are already correctly placed. -/
theorem SfClosed.insertR {R L : List Form} {X : Form} (h : SfClosed R L)
    (hand : ∀ A B : Form, X = .and A B → A ∈ R ∧ B ∈ R)
    (hor : ∀ A B : Form, X = .or A B → A ∈ R ∧ B ∈ R)
    (himp : ∀ A B : Form, X = .imp A B → A ∈ L ∧ B ∈ R) :
    SfClosed (X :: R) L := by
  have wk : ∀ {Y : Form}, Y ∈ R → Y ∈ X :: R := fun hY => List.mem_cons_of_mem _ hY
  constructor <;> intro A B hmem
  · rcases List.mem_cons.mp hmem with rfl | h'
    · exact ⟨wk (hand A B rfl).1, wk (hand A B rfl).2⟩
    · exact ⟨wk (h.rAnd h').1, wk (h.rAnd h').2⟩
  · rcases List.mem_cons.mp hmem with rfl | h'
    · exact ⟨wk (hor A B rfl).1, wk (hor A B rfl).2⟩
    · exact ⟨wk (h.rOr h').1, wk (h.rOr h').2⟩
  · rcases List.mem_cons.mp hmem with rfl | h'
    · exact ⟨(himp A B rfl).1, wk (himp A B rfl).2⟩
    · exact ⟨(h.rImp h').1, wk (h.rImp h').2⟩
  · exact ⟨(h.lAnd hmem).1, (h.lAnd hmem).2⟩
  · exact ⟨(h.lOr hmem).1, (h.lOr hmem).2⟩
  · exact ⟨wk (h.lImp hmem).1, (h.lImp hmem).2⟩

/-- Inserting a compound formula into the LEFT component, dually. -/
theorem SfClosed.insertL {R L : List Form} {X : Form} (h : SfClosed R L)
    (hand : ∀ A B : Form, X = .and A B → A ∈ L ∧ B ∈ L)
    (hor : ∀ A B : Form, X = .or A B → A ∈ L ∧ B ∈ L)
    (himp : ∀ A B : Form, X = .imp A B → A ∈ R ∧ B ∈ L) :
    SfClosed R (X :: L) := by
  have wk : ∀ {Y : Form}, Y ∈ L → Y ∈ X :: L := fun hY => List.mem_cons_of_mem _ hY
  constructor <;> intro A B hmem
  · exact ⟨(h.rAnd hmem).1, (h.rAnd hmem).2⟩
  · exact ⟨(h.rOr hmem).1, (h.rOr hmem).2⟩
  · exact ⟨wk (h.rImp hmem).1, (h.rImp hmem).2⟩
  · rcases List.mem_cons.mp hmem with rfl | h'
    · exact ⟨wk (hand A B rfl).1, wk (hand A B rfl).2⟩
    · exact ⟨wk (h.lAnd h').1, wk (h.lAnd h').2⟩
  · rcases List.mem_cons.mp hmem with rfl | h'
    · exact ⟨wk (hor A B rfl).1, wk (hor A B rfl).2⟩
    · exact ⟨wk (h.lOr h').1, wk (h.lOr h').2⟩
  · rcases List.mem_cons.mp hmem with rfl | h'
    · exact ⟨(himp A B rfl).1, wk (himp A B rfl).2⟩
    · exact ⟨(h.lImp h').1, wk (h.lImp h').2⟩

theorem self_mem_sfPos (X : Form) : X ∈ (sfPos X).1 := by
  cases X <;> simp [sfPos]

theorem self_mem_sfNeg (X : Form) : X ∈ (sfNeg X).2 := by
  cases X <;> simp [sfNeg]

mutual
  theorem sfPos_closed (X : Form) : SfClosed (sfPos X).1 (sfPos X).2 := by
    cases X with
    | atom p =>
        constructor <;> intro A B hmem <;> simp [sfPos] at hmem
    | bot =>
        constructor <;> intro A B hmem <;> simp [sfPos] at hmem
    | and A B =>
        have h := (sfPos_closed A).union (sfPos_closed B)
        refine (show SfClosed ((sfPos A).1 ++ (sfPos B).1) ((sfPos A).2 ++ (sfPos B).2) from h).insertR
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨List.mem_append_left _ (self_mem_sfPos A),
               List.mem_append_right _ (self_mem_sfPos B)⟩
    | or A B =>
        have h := (sfPos_closed A).union (sfPos_closed B)
        refine (show SfClosed ((sfPos A).1 ++ (sfPos B).1) ((sfPos A).2 ++ (sfPos B).2) from h).insertR
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨List.mem_append_left _ (self_mem_sfPos A),
               List.mem_append_right _ (self_mem_sfPos B)⟩
    | imp A B =>
        have h := (sfNeg_closed A).union (sfPos_closed B)
        refine (show SfClosed ((sfNeg A).1 ++ (sfPos B).1) ((sfNeg A).2 ++ (sfPos B).2) from h).insertR
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨List.mem_append_left _ (self_mem_sfNeg A),
               List.mem_append_right _ (self_mem_sfPos B)⟩

  theorem sfNeg_closed (X : Form) : SfClosed (sfNeg X).1 (sfNeg X).2 := by
    cases X with
    | atom p =>
        constructor <;> intro A B hmem <;> simp [sfNeg] at hmem
    | bot =>
        constructor <;> intro A B hmem <;> simp [sfNeg] at hmem
    | and A B =>
        have h := (sfNeg_closed A).union (sfNeg_closed B)
        refine (show SfClosed ((sfNeg A).1 ++ (sfNeg B).1) ((sfNeg A).2 ++ (sfNeg B).2) from h).insertL
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨List.mem_append_left _ (self_mem_sfNeg A),
               List.mem_append_right _ (self_mem_sfNeg B)⟩
    | or A B =>
        have h := (sfNeg_closed A).union (sfNeg_closed B)
        refine (show SfClosed ((sfNeg A).1 ++ (sfNeg B).1) ((sfNeg A).2 ++ (sfNeg B).2) from h).insertL
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨List.mem_append_left _ (self_mem_sfNeg A),
               List.mem_append_right _ (self_mem_sfNeg B)⟩
    | imp A B =>
        have h := (sfPos_closed A).union (sfNeg_closed B)
        refine (show SfClosed ((sfPos A).1 ++ (sfNeg B).1) ((sfPos A).2 ++ (sfNeg B).2) from h).insertL
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨List.mem_append_left _ (self_mem_sfPos A),
               List.mem_append_right _ (self_mem_sfNeg B)⟩
end

/-! The paper's four clauses, now as theorems about `sfR`/`sfL`. -/

theorem sfR_self (G : Form) : G ∈ sfR G := self_mem_sfPos G

theorem sfR_and {G A B : Form} (h : Form.and A B ∈ sfR G) :
    A ∈ sfR G ∧ B ∈ sfR G := (sfPos_closed G).rAnd h

theorem sfR_or {G A B : Form} (h : Form.or A B ∈ sfR G) :
    A ∈ sfR G ∧ B ∈ sfR G := (sfPos_closed G).rOr h

theorem sfR_imp {G A B : Form} (h : Form.imp A B ∈ sfR G) :
    A ∈ sfL G ∧ B ∈ sfR G := (sfPos_closed G).rImp h

theorem sfL_and {G A B : Form} (h : Form.and A B ∈ sfL G) :
    A ∈ sfL G ∧ B ∈ sfL G := (sfPos_closed G).lAnd h

theorem sfL_or {G A B : Form} (h : Form.or A B ∈ sfL G) :
    A ∈ sfL G ∧ B ∈ sfL G := (sfPos_closed G).lOr h

theorem sfL_imp {G A B : Form} (h : Form.imp A B ∈ sfL G) :
    A ∈ sfR G ∧ B ∈ sfL G := (sfPos_closed G).lImp h

/-! ### All subformulas

"Given a formula `G`, `Sf(G)` is the set of all subformulas of `G`
(including `G` itself)"; and "by `Sf⁻(C)` we denote the set
`Sf(C) \ {C}`". -/

/-- `Sf(A)`. -/
def sf : Form → List Form
  | .atom p => [Form.atom p]
  | .bot => [Form.bot]
  | .and A B => (Form.and A B) :: (sf A ++ sf B)
  | .or A B => (Form.or A B) :: (sf A ++ sf B)
  | .imp A B => (Form.imp A B) :: (sf A ++ sf B)

/-- `Sf⁻(A) = Sf(A) \ {A}`. -/
def sfm (A : Form) : List Form := rm (sf A) A

theorem self_mem_sf (A : Form) : A ∈ sf A := by
  cases A <;> simp [sf]

/-- Every subformula is no larger than the formula.  This is what makes
the `Sf⁻` inclusions between a compound and its components work. -/
theorem size_le_of_mem_sf : ∀ {A X : Form}, X ∈ sf A → X.size ≤ A.size := by
  intro A
  induction A with
  | atom p => intro X h; simp [sf] at h; subst h; simp [Form.size]
  | bot => intro X h; simp [sf] at h; subst h; simp [Form.size]
  | and A B ihA ihB =>
      intro X h
      simp only [sf, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp [Form.size]; omega)
  | or A B ihA ihB =>
      intro X h
      simp only [sf, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp [Form.size]; omega)
  | imp A B ihA ihB =>
      intro X h
      simp only [sf, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp [Form.size]; omega)

theorem sf_subset_sfm_impL {A B : Form} : sf A ⊆ sfm (.imp A B) := by
  intro X hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl hX)

/-- A PROPER subformula is strictly smaller.  The join case's secondary
induction on `size H` needs the strictness. -/
theorem size_lt_of_mem_sfm : ∀ {A X : Form}, X ∈ sfm A → X.size < A.size := by
  intro A
  induction A with
  | atom p => intro X h; simp [sfm, sf, rm] at h
  | bot => intro X h; simp [sfm, sf, rm] at h
  | and A B ihA ihB =>
      intro X h
      obtain ⟨hne, hmem⟩ := mem_rm.mp h
      simp only [sf, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hmem | hmem
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hmem; simp only [Form.size]; omega
      · have := size_le_of_mem_sf hmem; simp only [Form.size]; omega
  | or A B ihA ihB =>
      intro X h
      obtain ⟨hne, hmem⟩ := mem_rm.mp h
      simp only [sf, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hmem | hmem
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hmem; simp only [Form.size]; omega
      · have := size_le_of_mem_sf hmem; simp only [Form.size]; omega
  | imp A B ihA ihB =>
      intro X h
      obtain ⟨hne, hmem⟩ := mem_rm.mp h
      simp only [sf, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hmem | hmem
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hmem; simp only [Form.size]; omega
      · have := size_le_of_mem_sf hmem; simp only [Form.size]; omega

theorem sfm_subset_sfm_impR {A B : Form} : sfm B ⊆ sfm (.imp A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr hX')

theorem sfm_subset_sfm_and₁ {A B : Form} : sfm A ⊆ sfm (.and A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl hX')

theorem sfm_subset_sfm_and₂ {A B : Form} : sfm B ⊆ sfm (.and A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr hX')

theorem sfm_subset_sfm_or₁ {A B : Form} : sfm A ⊆ sfm (.or A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl hX')

theorem sfm_subset_sfm_or₂ {A B : Form} : sfm B ⊆ sfm (.or A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr hX')

/-! ## The sets `Ĝ_at`, `Ĝ_imp`, `Ĝ`

"`Ĝ_at = Sf^L(G) ∩ PV`,  `Ĝ_imp = Sf^L(G) ∩ Fm⊃`,  `Ĝ = Ĝ_at ++ Ĝ_imp`."
-/

/-- `Ĝ_at = Sf^L(G) ∩ PV`. -/
def gAt (G : Form) : List Form := (sfL G).filter Form.isPV

/-- `Ĝ_imp = Sf^L(G) ∩ Fm⊃`. -/
def gImp (G : Form) : List Form := (sfL G).filter Form.isImp

/-- `Ĝ = Ĝ_at ++ Ĝ_imp`. -/
def gHat (G : Form) : List Form := gAt G ++ gImp G

/-! ## Canonical contexts

Contexts denote *sets*, and the calculus needs one operation — the split
of an irregular zone as `Θ = Θ' ∪ Λ` in the `⊃∈` rule — to be an
equality of the rule's own INDEX, not merely an equality of member sets.
Lists do not give that: `++` is neither commutative nor idempotent.
`Finset` gave it because a `Finset` *is* a set.

The replacement, costing no `Classical.choice`: represent a context by
its filter of `Ĝ`.  This is legitimate exactly because every context
occurring in a derivation is a subset of `Ĝ` (`wfR`/`wfI`), so `nf G`
changes no context's membership — and two contexts with the same members
are then literally the same list. -/

/-- The canonical form of a context: the members of `Ĝ` lying in it. -/
def nf (G : Form) (l : List Form) : List Form :=
  (gHat G).filter (fun x => decide (x ∈ l))

@[simp] theorem mem_nf {G : Form} {l : List Form} {x : Form} :
    x ∈ nf G l ↔ (x ∈ gHat G ∧ x ∈ l) := by
  simp [nf, List.mem_filter]

/-- **Extensionality** — the property `++` lacks and `Finset` had:
canonical forms agree as soon as their members inside `Ĝ` agree. -/
theorem nf_ext {G : Form} {l m : List Form}
    (h : ∀ x, x ∈ gHat G → (x ∈ l ↔ x ∈ m)) : nf G l = nf G m := by
  refine List.filter_congr ?_
  intro x hx
  simp [h x hx]

theorem nf_idem {G : Form} {l : List Form} : nf G (nf G l) = nf G l :=
  nf_ext (fun x hx => by simp [hx])

theorem nf_subset {G : Form} {l : List Form} : nf G l ⊆ gHat G :=
  fun _ h => (mem_nf.mp h).1

theorem nf_subset_self {G : Form} {l : List Form} : nf G l ⊆ l :=
  fun _ h => (mem_nf.mp h).2

/-- On a context already inside `Ĝ`, canonicalisation changes nothing
that membership can see. -/
theorem mem_nf_of_subset {G : Form} {l : List Form} (hl : l ⊆ gHat G)
    {x : Form} : x ∈ nf G l ↔ x ∈ l :=
  ⟨fun h => (mem_nf.mp h).2, fun h => mem_nf.mpr ⟨hl h, h⟩⟩

/-- The atomic part of a set of formulas: the paper's notation `Γ^at`,
which means "`Γ^at ⊆ PV`".  For `Γ ⊆ Ĝ` the decomposition
`Γ = Γ^at ++ Γ^⊃` is unique, so taking it by `filter` is definitional. -/
def atPart (Γ : List Form) : List Form := Γ.filter Form.isPV

/-- The implicational part of a set of formulas: the paper's `Γ^⊃`. -/
def impPart (Γ : List Form) : List Form := Γ.filter Form.isImp

/-! ## The closure `Cl(Γ)`

"The closure of `Γ`, denoted by `Cl(Γ)`, is the smallest set containing
the formulas `X` defined by the following grammar:

    X ::= C | X ∧ X | A ∨ X | X ∨ A | A ⊃ X       (C ∈ Γ, A any formula)"
-/

/-- `Cl(Γ)`, as the inductive family generated by the paper's grammar. -/
inductive Clo (Γ : List Form) : Form → Prop
  | base {C : Form} : C ∈ Γ → Clo Γ C
  | and {X Y : Form} : Clo Γ X → Clo Γ Y → Clo Γ (.and X Y)
  | orR {A X : Form} : Clo Γ X → Clo Γ (.or A X)
  | orL {A X : Form} : Clo Γ X → Clo Γ (.or X A)
  | imp {A X : Form} : Clo Γ X → Clo Γ (.imp A X)

/-! ### Properties (Cl1)–(Cl6)

"The following properties of closures can be easily proved." -/

/-- **(Cl1)** `K,α ⊩ Γ` implies `K,α ⊩ Cl(Γ)`. -/
theorem clo_forces {K : Kripke} {a : K.W} {Γ : List Form}
    (h : K.forces a Γ) : ∀ {X : Form}, Clo Γ X → K.force a X := by
  intro X hX
  induction hX with
  | base hC => exact h _ hC
  | and _ _ ihX ihY => exact ⟨ihX, ihY⟩
  | orR _ ih => exact Or.inr ih
  | orL _ ih => exact Or.inl ih
  | imp _ ih => exact fun b hb _ => K.force_mono hb ih

/-- **(Cl3)**, first half: `Γ ⊆ Cl(Γ)`. -/
theorem clo_subset {Γ : List Form} {C : Form} (h : C ∈ Γ) : Clo Γ C :=
  .base h

/-- **(Cl4)** `Γ₁ ⊆ Γ₂` implies `Cl(Γ₁) ⊆ Cl(Γ₂)`. -/
theorem clo_mono {Γ₁ Γ₂ : List Form} (hsub : Γ₁ ⊆ Γ₂) {X : Form}
    (h : Clo Γ₁ X) : Clo Γ₂ X := by
  induction h with
  | base hC => exact .base (hsub hC)
  | and _ _ ihX ihY => exact .and ihX ihY
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih

/-- **(Cl5)** `Cl(Γ) ∩ PV = Γ ∩ PV`.  Stated as: a propositional variable
lies in `Cl(Γ)` only if it already lies in `Γ`. -/
theorem clo_pv {Γ : List Form} {p : String} (h : Clo Γ (.atom p)) :
    Form.atom p ∈ Γ := by
  cases h with
  | base hC => exact hC

/-- **(Cl6)** `Γ₁ ⊆ Cl(Γ₂)` implies `Cl(Γ₁) ⊆ Cl(Γ₂)`.  "This follows
from (Cl3) and (Cl4)." -/
theorem clo_trans {Γ Δ : List Form} (h : ∀ X ∈ Δ, Clo Γ X) :
    ∀ {A : Form}, Clo Δ A → Clo Γ A := by
  intro A hA
  induction hA with
  | base hC => exact h _ hC
  | and _ _ ihX ihY => exact .and ihX ihY
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih

/-- **(Cl2)** `A ∈ Cl(Γ)` implies `A ∈ Cl(Γ ∩ Sf(A))`.  Consumed by the
irregular `⊃∈` case of the soundness proof. -/
theorem clo_sf {Γ : List Form} : ∀ {A : Form}, Clo Γ A → Clo (cap Γ (sf A)) A := by
  intro A h
  induction h with
  | @base C hC => exact .base (mem_cap.mpr ⟨hC, self_mem_sf C⟩)
  | @and X Y _ _ ihX ihY =>
      refine .and (clo_mono ?_ ihX) (clo_mono ?_ ihY)
      · exact cap_subset_cap (by
          intro Z hZ
          simp only [sf, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl hZ))
      · exact cap_subset_cap (by
          intro Z hZ
          simp only [sf, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr hZ))
  | @orR A X _ ih =>
      refine .orR (clo_mono ?_ ih)
      exact cap_subset_cap (by
        intro Z hZ
        simp only [sf, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hZ))
  | @orL A X _ ih =>
      refine .orL (clo_mono ?_ ih)
      exact cap_subset_cap (by
        intro Z hZ
        simp only [sf, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hZ))
  | @imp A X _ ih =>
      refine .imp (clo_mono ?_ ih)
      exact cap_subset_cap (by
        intro Z hZ
        simp only [sf, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hZ))

end FRJ
