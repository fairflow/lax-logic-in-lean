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
def isPV : Form → Prop
  | .atom _ => True
  | _ => False

instance (A : Form) : Decidable A.isPV := by
  cases A <;> unfold isPV <;> infer_instance

/-- "By `Prime` we denote the set `PV ∪ {⊥}`." -/
def isPrime : Form → Prop
  | .atom _ => True
  | .bot => True
  | _ => False

instance (A : Form) : Decidable A.isPrime := by
  cases A <;> unfold isPrime <;> infer_instance

/-- "By `Fm⊃` [we denote] the set of ⊃-formulas of `L`." -/
def isImp : Form → Prop
  | .imp _ _ => True
  | _ => False

instance (A : Form) : Decidable A.isImp := by
  cases A <;> unfold isImp <;> infer_instance

theorem isPV_isPrime {A : Form} (h : A.isPV) : A.isPrime := by
  cases A <;> simp_all [isPV, isPrime]

end Form

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
  /-- "⟨P,≤⟩ is a finite poset" -/
  finite : Finite W
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

attribute [instance] Kripke.finite

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

/-- "`K,α ⊩ Γ` means `K,α ⊩ A` for every `A ∈ Γ`." -/
def forces (a : K.W) (Γ : Finset Form) : Prop := ∀ A ∈ Γ, K.force a A

theorem forces_mono {a b : K.W} (hab : K.le a b) {Γ : Finset Form}
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
  def sfPos : Form → Finset Form × Finset Form
    | .atom p => ({.atom p}, ∅)
    | .bot => ({.bot}, ∅)
    | .and A B =>
        (insert (.and A B) ((sfPos A).1 ∪ (sfPos B).1), (sfPos A).2 ∪ (sfPos B).2)
    | .or A B =>
        (insert (.or A B) ((sfPos A).1 ∪ (sfPos B).1), (sfPos A).2 ∪ (sfPos B).2)
    | .imp A B =>
        (insert (.imp A B) ((sfNeg A).1 ∪ (sfPos B).1), (sfNeg A).2 ∪ (sfPos B).2)

  /-- The `(Sf^R, Sf^L)` contribution of a formula occurring in LEFT position. -/
  def sfNeg : Form → Finset Form × Finset Form
    | .atom p => (∅, {.atom p})
    | .bot => (∅, {.bot})
    | .and A B =>
        ((sfNeg A).1 ∪ (sfNeg B).1, insert (.and A B) ((sfNeg A).2 ∪ (sfNeg B).2))
    | .or A B =>
        ((sfNeg A).1 ∪ (sfNeg B).1, insert (.or A B) ((sfNeg A).2 ∪ (sfNeg B).2))
    | .imp A B =>
        ((sfPos A).1 ∪ (sfNeg B).1, insert (.imp A B) ((sfPos A).2 ∪ (sfNeg B).2))
end

/-- `Sf^R(G)`, the right (positive) subformulas of `G`. -/
def sfR (G : Form) : Finset Form := (sfPos G).1

/-- `Sf^L(G)`, the left (negative) subformulas of `G`. -/
def sfL (G : Form) : Finset Form := (sfPos G).2

/-! ### The characterisation, as the paper states it

These four theorems are the fidelity check on `sfR`/`sfL`: they are the
paper's four defining clauses, proved of our computed sets.
-/

/-- The paper's four defining clauses, as a property of a pair of sets
`(R, L)` standing for `(Sf^R(G), Sf^L(G))`. -/
structure SfClosed (R L : Finset Form) : Prop where
  rAnd : ∀ {A B : Form}, Form.and A B ∈ R → A ∈ R ∧ B ∈ R
  rOr : ∀ {A B : Form}, Form.or A B ∈ R → A ∈ R ∧ B ∈ R
  rImp : ∀ {A B : Form}, Form.imp A B ∈ R → A ∈ L ∧ B ∈ R
  lAnd : ∀ {A B : Form}, Form.and A B ∈ L → A ∈ L ∧ B ∈ L
  lOr : ∀ {A B : Form}, Form.or A B ∈ L → A ∈ L ∧ B ∈ L
  lImp : ∀ {A B : Form}, Form.imp A B ∈ L → A ∈ R ∧ B ∈ L

theorem SfClosed.union {R₁ L₁ R₂ L₂ : Finset Form}
    (h₁ : SfClosed R₁ L₁) (h₂ : SfClosed R₂ L₂) :
    SfClosed (R₁ ∪ R₂) (L₁ ∪ L₂) := by
  constructor <;> intro A B hmem <;>
    rcases Finset.mem_union.mp hmem with h | h
  · exact ⟨Finset.mem_union_left _ (h₁.rAnd h).1, Finset.mem_union_left _ (h₁.rAnd h).2⟩
  · exact ⟨Finset.mem_union_right _ (h₂.rAnd h).1, Finset.mem_union_right _ (h₂.rAnd h).2⟩
  · exact ⟨Finset.mem_union_left _ (h₁.rOr h).1, Finset.mem_union_left _ (h₁.rOr h).2⟩
  · exact ⟨Finset.mem_union_right _ (h₂.rOr h).1, Finset.mem_union_right _ (h₂.rOr h).2⟩
  · exact ⟨Finset.mem_union_left _ (h₁.rImp h).1, Finset.mem_union_left _ (h₁.rImp h).2⟩
  · exact ⟨Finset.mem_union_right _ (h₂.rImp h).1, Finset.mem_union_right _ (h₂.rImp h).2⟩
  · exact ⟨Finset.mem_union_left _ (h₁.lAnd h).1, Finset.mem_union_left _ (h₁.lAnd h).2⟩
  · exact ⟨Finset.mem_union_right _ (h₂.lAnd h).1, Finset.mem_union_right _ (h₂.lAnd h).2⟩
  · exact ⟨Finset.mem_union_left _ (h₁.lOr h).1, Finset.mem_union_left _ (h₁.lOr h).2⟩
  · exact ⟨Finset.mem_union_right _ (h₂.lOr h).1, Finset.mem_union_right _ (h₂.lOr h).2⟩
  · exact ⟨Finset.mem_union_left _ (h₁.lImp h).1, Finset.mem_union_left _ (h₁.lImp h).2⟩
  · exact ⟨Finset.mem_union_right _ (h₂.lImp h).1, Finset.mem_union_right _ (h₂.lImp h).2⟩

/-- Inserting a compound formula into the RIGHT component preserves the
clauses, provided its own components are already correctly placed. -/
theorem SfClosed.insertR {R L : Finset Form} {X : Form} (h : SfClosed R L)
    (hand : ∀ A B : Form, X = .and A B → A ∈ R ∧ B ∈ R)
    (hor : ∀ A B : Form, X = .or A B → A ∈ R ∧ B ∈ R)
    (himp : ∀ A B : Form, X = .imp A B → A ∈ L ∧ B ∈ R) :
    SfClosed (insert X R) L := by
  have wk : ∀ {Y : Form}, Y ∈ R → Y ∈ insert X R := fun hY => Finset.mem_insert_of_mem hY
  constructor <;> intro A B hmem
  · rcases Finset.mem_insert.mp hmem with rfl | h'
    · exact ⟨wk (hand A B rfl).1, wk (hand A B rfl).2⟩
    · exact ⟨wk (h.rAnd h').1, wk (h.rAnd h').2⟩
  · rcases Finset.mem_insert.mp hmem with rfl | h'
    · exact ⟨wk (hor A B rfl).1, wk (hor A B rfl).2⟩
    · exact ⟨wk (h.rOr h').1, wk (h.rOr h').2⟩
  · rcases Finset.mem_insert.mp hmem with rfl | h'
    · exact ⟨(himp A B rfl).1, wk (himp A B rfl).2⟩
    · exact ⟨(h.rImp h').1, wk (h.rImp h').2⟩
  · exact ⟨(h.lAnd hmem).1, (h.lAnd hmem).2⟩
  · exact ⟨(h.lOr hmem).1, (h.lOr hmem).2⟩
  · exact ⟨wk (h.lImp hmem).1, (h.lImp hmem).2⟩

/-- Inserting a compound formula into the LEFT component, dually. -/
theorem SfClosed.insertL {R L : Finset Form} {X : Form} (h : SfClosed R L)
    (hand : ∀ A B : Form, X = .and A B → A ∈ L ∧ B ∈ L)
    (hor : ∀ A B : Form, X = .or A B → A ∈ L ∧ B ∈ L)
    (himp : ∀ A B : Form, X = .imp A B → A ∈ R ∧ B ∈ L) :
    SfClosed R (insert X L) := by
  have wk : ∀ {Y : Form}, Y ∈ L → Y ∈ insert X L := fun hY => Finset.mem_insert_of_mem hY
  constructor <;> intro A B hmem
  · exact ⟨(h.rAnd hmem).1, (h.rAnd hmem).2⟩
  · exact ⟨(h.rOr hmem).1, (h.rOr hmem).2⟩
  · exact ⟨wk (h.rImp hmem).1, (h.rImp hmem).2⟩
  · rcases Finset.mem_insert.mp hmem with rfl | h'
    · exact ⟨wk (hand A B rfl).1, wk (hand A B rfl).2⟩
    · exact ⟨wk (h.lAnd h').1, wk (h.lAnd h').2⟩
  · rcases Finset.mem_insert.mp hmem with rfl | h'
    · exact ⟨wk (hor A B rfl).1, wk (hor A B rfl).2⟩
    · exact ⟨wk (h.lOr h').1, wk (h.lOr h').2⟩
  · rcases Finset.mem_insert.mp hmem with rfl | h'
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
        refine (show SfClosed ((sfPos A).1 ∪ (sfPos B).1) ((sfPos A).2 ∪ (sfPos B).2) from h).insertR
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨Finset.mem_union_left _ (self_mem_sfPos A),
               Finset.mem_union_right _ (self_mem_sfPos B)⟩
    | or A B =>
        have h := (sfPos_closed A).union (sfPos_closed B)
        refine (show SfClosed ((sfPos A).1 ∪ (sfPos B).1) ((sfPos A).2 ∪ (sfPos B).2) from h).insertR
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨Finset.mem_union_left _ (self_mem_sfPos A),
               Finset.mem_union_right _ (self_mem_sfPos B)⟩
    | imp A B =>
        have h := (sfNeg_closed A).union (sfPos_closed B)
        refine (show SfClosed ((sfNeg A).1 ∪ (sfPos B).1) ((sfNeg A).2 ∪ (sfPos B).2) from h).insertR
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨Finset.mem_union_left _ (self_mem_sfNeg A),
               Finset.mem_union_right _ (self_mem_sfPos B)⟩

  theorem sfNeg_closed (X : Form) : SfClosed (sfNeg X).1 (sfNeg X).2 := by
    cases X with
    | atom p =>
        constructor <;> intro A B hmem <;> simp [sfNeg] at hmem
    | bot =>
        constructor <;> intro A B hmem <;> simp [sfNeg] at hmem
    | and A B =>
        have h := (sfNeg_closed A).union (sfNeg_closed B)
        refine (show SfClosed ((sfNeg A).1 ∪ (sfNeg B).1) ((sfNeg A).2 ∪ (sfNeg B).2) from h).insertL
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨Finset.mem_union_left _ (self_mem_sfNeg A),
               Finset.mem_union_right _ (self_mem_sfNeg B)⟩
    | or A B =>
        have h := (sfNeg_closed A).union (sfNeg_closed B)
        refine (show SfClosed ((sfNeg A).1 ∪ (sfNeg B).1) ((sfNeg A).2 ∪ (sfNeg B).2) from h).insertL
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨Finset.mem_union_left _ (self_mem_sfNeg A),
               Finset.mem_union_right _ (self_mem_sfNeg B)⟩
    | imp A B =>
        have h := (sfPos_closed A).union (sfNeg_closed B)
        refine (show SfClosed ((sfPos A).1 ∪ (sfNeg B).1) ((sfPos A).2 ∪ (sfNeg B).2) from h).insertL
          ?_ ?_ ?_ <;> intro C D heq <;> cases heq
        exact ⟨Finset.mem_union_left _ (self_mem_sfPos A),
               Finset.mem_union_right _ (self_mem_sfNeg B)⟩
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
def sf : Form → Finset Form
  | .atom p => {.atom p}
  | .bot => {.bot}
  | .and A B => insert (.and A B) (sf A ∪ sf B)
  | .or A B => insert (.or A B) (sf A ∪ sf B)
  | .imp A B => insert (.imp A B) (sf A ∪ sf B)

/-- `Sf⁻(A) = Sf(A) \ {A}`. -/
def sfm (A : Form) : Finset Form := (sf A).erase A

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
      simp only [sf, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp [Form.size]; omega)
  | or A B ihA ihB =>
      intro X h
      simp only [sf, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp [Form.size]; omega)
  | imp A B ihA ihB =>
      intro X h
      simp only [sf, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp [Form.size]; omega)

theorem sf_subset_sfm_impL {A B : Form} : sf A ⊆ sfm (.imp A B) := by
  intro X hX
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl hX)

theorem sfm_subset_sfm_and₁ {A B : Form} : sfm A ⊆ sfm (.and A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := Finset.mem_erase.mp hX
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl hX')

theorem sfm_subset_sfm_and₂ {A B : Form} : sfm B ⊆ sfm (.and A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := Finset.mem_erase.mp hX
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr hX')

theorem sfm_subset_sfm_or₁ {A B : Form} : sfm A ⊆ sfm (.or A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := Finset.mem_erase.mp hX
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl hX')

theorem sfm_subset_sfm_or₂ {A B : Form} : sfm B ⊆ sfm (.or A B) := by
  intro X hX
  obtain ⟨-, hX'⟩ := Finset.mem_erase.mp hX
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hcon
    have := size_le_of_mem_sf hX'
    rw [hcon] at this
    simp only [Form.size] at this
    omega
  · simp only [sf, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr hX')

/-! ## The sets `Ĝ_at`, `Ĝ_imp`, `Ĝ`

"`Ĝ_at = Sf^L(G) ∩ PV`,  `Ĝ_imp = Sf^L(G) ∩ Fm⊃`,  `Ĝ = Ĝ_at ∪ Ĝ_imp`."
-/

/-- `Ĝ_at = Sf^L(G) ∩ PV`. -/
def gAt (G : Form) : Finset Form := (sfL G).filter Form.isPV

/-- `Ĝ_imp = Sf^L(G) ∩ Fm⊃`. -/
def gImp (G : Form) : Finset Form := (sfL G).filter Form.isImp

/-- `Ĝ = Ĝ_at ∪ Ĝ_imp`. -/
def gHat (G : Form) : Finset Form := gAt G ∪ gImp G

/-- The atomic part of a set of formulas: the paper's notation `Γ^at`,
which means "`Γ^at ⊆ PV`".  For `Γ ⊆ Ĝ` the decomposition
`Γ = Γ^at ∪ Γ^⊃` is unique, so taking it by `filter` is definitional. -/
def atPart (Γ : Finset Form) : Finset Form := Γ.filter Form.isPV

/-- The implicational part of a set of formulas: the paper's `Γ^⊃`. -/
def impPart (Γ : Finset Form) : Finset Form := Γ.filter Form.isImp

/-! ## The closure `Cl(Γ)`

"The closure of `Γ`, denoted by `Cl(Γ)`, is the smallest set containing
the formulas `X` defined by the following grammar:

    X ::= C | X ∧ X | A ∨ X | X ∨ A | A ⊃ X       (C ∈ Γ, A any formula)"
-/

/-- `Cl(Γ)`, as the inductive family generated by the paper's grammar. -/
inductive Clo (Γ : Finset Form) : Form → Prop
  | base {C : Form} : C ∈ Γ → Clo Γ C
  | and {X Y : Form} : Clo Γ X → Clo Γ Y → Clo Γ (.and X Y)
  | orR {A X : Form} : Clo Γ X → Clo Γ (.or A X)
  | orL {A X : Form} : Clo Γ X → Clo Γ (.or X A)
  | imp {A X : Form} : Clo Γ X → Clo Γ (.imp A X)

/-! ### Properties (Cl1)–(Cl6)

"The following properties of closures can be easily proved." -/

/-- **(Cl1)** `K,α ⊩ Γ` implies `K,α ⊩ Cl(Γ)`. -/
theorem clo_forces {K : Kripke} {a : K.W} {Γ : Finset Form}
    (h : K.forces a Γ) : ∀ {X : Form}, Clo Γ X → K.force a X := by
  intro X hX
  induction hX with
  | base hC => exact h _ hC
  | and _ _ ihX ihY => exact ⟨ihX, ihY⟩
  | orR _ ih => exact Or.inr ih
  | orL _ ih => exact Or.inl ih
  | imp _ ih => exact fun b hb _ => K.force_mono hb ih

/-- **(Cl3)**, first half: `Γ ⊆ Cl(Γ)`. -/
theorem clo_subset {Γ : Finset Form} {C : Form} (h : C ∈ Γ) : Clo Γ C :=
  .base h

/-- **(Cl4)** `Γ₁ ⊆ Γ₂` implies `Cl(Γ₁) ⊆ Cl(Γ₂)`. -/
theorem clo_mono {Γ₁ Γ₂ : Finset Form} (hsub : Γ₁ ⊆ Γ₂) {X : Form}
    (h : Clo Γ₁ X) : Clo Γ₂ X := by
  induction h with
  | base hC => exact .base (hsub hC)
  | and _ _ ihX ihY => exact .and ihX ihY
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih

/-- **(Cl5)** `Cl(Γ) ∩ PV = Γ ∩ PV`.  Stated as: a propositional variable
lies in `Cl(Γ)` only if it already lies in `Γ`. -/
theorem clo_pv {Γ : Finset Form} {p : String} (h : Clo Γ (.atom p)) :
    Form.atom p ∈ Γ := by
  cases h with
  | base hC => exact hC

/-- **(Cl2)** `A ∈ Cl(Γ)` implies `A ∈ Cl(Γ ∩ Sf(A))`.  Consumed by the
irregular `⊃∈` case of the soundness proof. -/
theorem clo_sf {Γ : Finset Form} : ∀ {A : Form}, Clo Γ A → Clo (Γ ∩ sf A) A := by
  intro A h
  induction h with
  | @base C hC => exact .base (Finset.mem_inter.mpr ⟨hC, self_mem_sf C⟩)
  | @and X Y _ _ ihX ihY =>
      refine .and (clo_mono ?_ ihX) (clo_mono ?_ ihY)
      · exact Finset.inter_subset_inter_left (by
          intro Z hZ
          simp only [sf, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inl hZ))
      · exact Finset.inter_subset_inter_left (by
          intro Z hZ
          simp only [sf, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr hZ))
  | @orR A X _ ih =>
      refine .orR (clo_mono ?_ ih)
      exact Finset.inter_subset_inter_left (by
        intro Z hZ
        simp only [sf, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr hZ))
  | @orL A X _ ih =>
      refine .orL (clo_mono ?_ ih)
      exact Finset.inter_subset_inter_left (by
        intro Z hZ
        simp only [sf, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hZ))
  | @imp A X _ ih =>
      refine .imp (clo_mono ?_ ih)
      exact Finset.inter_subset_inter_left (by
        intro Z hZ
        simp only [sf, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inr hZ))

end FRJ
