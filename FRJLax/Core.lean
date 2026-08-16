/-
# FRJ◯ — the language, its subformulas, and the closure `Cl`

Section 2 of

  Camillo Fiorentini and Mauro Ferrari,
  *Duality between Unprovability and Provability in Forward
  Refutation-search for IPL*, ACM TOCL 21(3), Article 22, 2020,

clause by clause, over a language that carries the lax modality `◯` from
line one.  Numbering throughout is the **published journal's**; the
transcription was cross-read against the arXiv LaTeX source
(arXiv:1804.06689, `frj-corr.tex`), which is a close variant and not the
same text.  See `docs/frj-lax-plan.md` for the full plan, the numbering
table and the divergence list.

**Zero imports**, on the model of `LaxLogic/LJFOCore.lean`: no other
calculus in this repo can carry any part of the syntax or the closure.
No `Finset` anywhere — Mathlib's `Finset` union, erase and image report
`Classical.choice` at the definition level, so a term that merely
mentions them carries choice however it is proved.  Sets of formulas are
`List`s, used only up to membership.

**What is the paper's and what is ours.**  Everything here is the
paper's, over a larger language, except where marked `EXTENSION`.  There
are exactly two such marks, both in the subformula sets, and neither
touches the closure `Cl`, whose grammar is transcribed verbatim.  The
modal *rules* are W5 and are Matthew's; nothing here proposes one.
-/

namespace FRJLax

/-! ## The language `L`

"We consider the propositional language `L` based on a denumerable set of
propositional variables `PV`, the connectives `∧`, `∨`, `⊃` and the
logical constant `⊥`; `¬A` is a shorthand for `A ⊃ ⊥`."

To which this development adds the unary `◯` of Propositional Lax Logic.
-/

/-- Formulas of `L`, with `◯`.  Propositional variables are named by
strings, the repo's standing convention for a denumerable `PV`. -/
inductive Form where
  | atom : String → Form
  | bot : Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
  | circ : Form → Form
  deriving DecidableEq, Repr

namespace Form

/-- "`¬A` is a shorthand for `A ⊃ ⊥`." -/
def neg (A : Form) : Form := .imp A .bot

/-- "By `|A|` we denote the *size* of `A`, namely the number of symbols
in `A`." -/
def size : Form → Nat
  | .atom _ => 1
  | .bot => 1
  | .and A B => size A + size B + 1
  | .or A B => size A + size B + 1
  | .imp A B => size A + size B + 1
  | .circ A => size A + 1

theorem size_pos (A : Form) : 0 < A.size := by
  cases A <;> simp only [size] <;> omega

/-- `A ∈ PV`.  A `Bool`, not a `Prop`: shape predicates are decided, never
proved. -/
def isPV : Form → Bool
  | .atom _ => true
  | _ => false

/-- "By `Prime` we denote the set `PV ∪ {⊥}`." -/
def isPrime : Form → Bool
  | .atom _ => true
  | .bot => true
  | _ => false

/-- "By `Fm⊃` [we denote] the set of `⊃`-formulas of `L`." -/
def isImp : Form → Bool
  | .imp _ _ => true
  | _ => false

/-- The `◯`-formulas.  Not the paper's: vocabulary for W5, unused by the
`◯`-free layer.  See the note on the third zone at the end of this file. -/
def isCirc : Form → Bool
  | .circ _ => true
  | _ => false

theorem isPV_isPrime {A : Form} (h : A.isPV = true) : A.isPrime = true := by
  cases A <;> simp_all [isPV, isPrime]

theorem isPrime_not_isImp {A : Form} (h : A.isPrime = true) : A.isImp = false := by
  cases A <;> simp_all [isPrime, isImp]

theorem isPrime_not_isCirc {A : Form} (h : A.isPrime = true) : A.isCirc = false := by
  cases A <;> simp_all [isPrime, isCirc]

end Form

/-! ## Sets of formulas as lists

The development uses sets only up to membership, so lists serve.  This is
not a stylistic choice: `Finset.instUnion`, `Finset.erase`,
`Finset.image` and `Multiset.ndunion` each report `Classical.choice` at
the definition level.  `List.dedup` and `List.erase` are classical too;
filtering replaces both. -/

/-- Removal of a single element; `Finset.erase`'s replacement. -/
def rm (l : List Form) (x : Form) : List Form := l.filter (fun y => decide (y ≠ x))

@[simp] theorem mem_rm {l : List Form} {x y : Form} :
    y ∈ rm l x ↔ (y ≠ x ∧ y ∈ l) := by
  simp only [rm, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem rm_subset {l : List Form} {x : Form} : rm l x ⊆ l :=
  fun _ h => (mem_rm.mp h).2

theorem notMem_rm {l : List Form} {x : Form} : x ∉ rm l x :=
  fun h => (mem_rm.mp h).1 rfl

/-- Intersection; `Finset.inter`'s replacement. -/
def cap (l m : List Form) : List Form := l.filter (fun y => decide (y ∈ m))

@[simp] theorem mem_cap {l m : List Form} {y : Form} :
    y ∈ cap l m ↔ (y ∈ l ∧ y ∈ m) := by
  simp [cap, List.mem_filter]

theorem cap_subset_left {l m : List Form} : cap l m ⊆ l :=
  fun _ h => (mem_cap.mp h).1

theorem cap_subset_right {l m : List Form} : cap l m ⊆ m :=
  fun _ h => (mem_cap.mp h).2

theorem cap_mono {l l' m m' : List Form} (hl : l ⊆ l') (hm : m ⊆ m') :
    cap l m ⊆ cap l' m' :=
  fun _ h => mem_cap.mpr ⟨hl (mem_cap.mp h).1, hm (mem_cap.mp h).2⟩

/-- Equality up to membership.  Every computed context in the rule table
enters through this relation rather than through a computed index, which
is what keeps the inductive family free of green slime and removes all
order dependence. -/
def Eqv (l m : List Form) : Prop := l ⊆ m ∧ m ⊆ l

@[inherit_doc] infix:50 " ≐ " => Eqv

theorem Eqv.refl (l : List Form) : l ≐ l := ⟨fun _ h => h, fun _ h => h⟩

theorem Eqv.symm {l m : List Form} (h : l ≐ m) : m ≐ l := ⟨h.2, h.1⟩

theorem Eqv.trans {l m n : List Form} (h₁ : l ≐ m) (h₂ : m ≐ n) : l ≐ n :=
  ⟨fun _ hx => h₂.1 (h₁.1 hx), fun _ hx => h₁.2 (h₂.2 hx)⟩

theorem Eqv.mem {l m : List Form} (h : l ≐ m) {x : Form} : x ∈ l ↔ x ∈ m :=
  ⟨fun hx => h.1 hx, fun hx => h.2 hx⟩

/-! ## Subformulas

"Given a formula `G`, `Sf(G)` is the set of all subformulas of `G`
(including `G` itself)"; `Sf⁻(C) = Sf(C) \ {C}`. -/

/-- `Sf(A)`. -/
def sf : Form → List Form
  | .atom a => [.atom a]
  | .bot => [.bot]
  | .and A B => .and A B :: (sf A ++ sf B)
  | .or A B => .or A B :: (sf A ++ sf B)
  | .imp A B => .imp A B :: (sf A ++ sf B)
  | .circ A => .circ A :: sf A

/-- `Sf⁻(A) = Sf(A) \ {A}`. -/
def sfm (A : Form) : List Form := rm (sf A) A

theorem self_mem_sf (A : Form) : A ∈ sf A := by
  cases A <;> simp [sf]

theorem size_le_of_mem_sf : ∀ {A X : Form}, X ∈ sf A → X.size ≤ A.size := by
  intro A
  induction A with
  | atom a => intro X h; simp [sf] at h; subst h; exact Nat.le_refl _
  | bot => intro X h; simp [sf] at h; subst h; exact Nat.le_refl _
  | and A B ihA ihB =>
      intro X h
      simp only [sf, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp only [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp only [Form.size]; omega)
  | or A B ihA ihB =>
      intro X h
      simp only [sf, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp only [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp only [Form.size]; omega)
  | imp A B ihA ihB =>
      intro X h
      simp only [sf, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp only [Form.size]; omega)
      · exact Nat.le_trans (ihB h) (by simp only [Form.size]; omega)
  | circ A ihA =>
      intro X h
      simp only [sf, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (ihA h) (by simp only [Form.size]; omega)

theorem size_lt_of_mem_sfm : ∀ {A X : Form}, X ∈ sfm A → X.size < A.size := by
  intro A X h
  have h' := mem_rm.mp h
  have hne : X ≠ A := h'.1
  have hmem : X ∈ sf A := h'.2
  cases A with
  | atom a => simp [sf] at hmem; exact absurd hmem hne
  | bot => simp [sf] at hmem; exact absurd hmem hne
  | and A B =>
      simp only [sf, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hm | hm
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega
  | or A B =>
      simp only [sf, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hm | hm
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega
  | imp A B =>
      simp only [sf, List.mem_cons, List.mem_append] at hmem
      rcases hmem with rfl | hm | hm
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega
  | circ A =>
      simp only [sf, List.mem_cons] at hmem
      rcases hmem with rfl | hm
      · exact absurd rfl hne
      · have := size_le_of_mem_sf hm; simp only [Form.size]; omega

/-- `Sf(A) ⊆ Sf⁻(A ⊃ B)`: the antecedent's subformulas are proper
subformulas of the implication.  This is what the join case of the
soundness lemma consumes. -/
theorem sf_subset_sfm_impL {A B : Form} : sf A ⊆ sfm (.imp A B) := by
  intro X hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf hX
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr (Or.inl hX)

theorem sfm_subset_sfm_impR {A B : Form} : sfm B ⊆ sfm (.imp A B) := by
  intro X hX
  have h' := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf h'.2
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr (Or.inr h'.2)

theorem sfm_subset_sfm_and₁ {A B : Form} : sfm A ⊆ sfm (.and A B) := by
  intro X hX
  have h' := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf h'.2
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr (Or.inl h'.2)

theorem sfm_subset_sfm_and₂ {A B : Form} : sfm B ⊆ sfm (.and A B) := by
  intro X hX
  have h' := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf h'.2
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr (Or.inr h'.2)

theorem sfm_subset_sfm_or₁ {A B : Form} : sfm A ⊆ sfm (.or A B) := by
  intro X hX
  have h' := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf h'.2
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr (Or.inl h'.2)

theorem sfm_subset_sfm_or₂ {A B : Form} : sfm B ⊆ sfm (.or A B) := by
  intro X hX
  have h' := mem_rm.mp hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf h'.2
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr (Or.inr h'.2)

/-- `Sf(A) ⊆ Sf⁻(◯A)`.  Ours, by the same computation as the others. -/
theorem sf_subset_sfm_circ {A : Form} : sf A ⊆ sfm (.circ A) := by
  intro X hX
  refine mem_rm.mpr ⟨?_, ?_⟩
  · intro hEq
    have := size_le_of_mem_sf hX
    rw [hEq] at this
    simp only [Form.size] at this
    omega
  · simp [sf]; exact Or.inr hX


/-! ## Left and right subformulas

"By `Sf^L(G)` and `Sf^R(G)` we denote the subsets of *left* and *right*
subformulas of `G` (a.k.a. negative/positive subformulas).  Formally,
`Sf^L(G)` and `Sf^R(G)` are the smallest subsets of `Sf(G)` such that:

* `G ∈ Sf^R(G)`;
* `A ⊙ B ∈ Sx(G)` implies `{A,B} ⊆ Sx(G)`, where `⊙ ∈ {∧,∨}` and
  `Sx ∈ {Sl,Sr}`;
* `A ⊃ B ∈ Sf^L(G)` implies `B ∈ Sf^L(G)` and `A ∈ Sf^R(G)`;
* `A ⊃ B ∈ Sf^R(G)` implies `B ∈ Sf^R(G)` and `A ∈ Sf^L(G)`."

**EXTENSION (ours, not the paper's).**  One clause is added for `◯`:

    ◯A ∈ Sx(G)  implies  A ∈ Sx(G),     Sx ∈ {Sf^L, Sf^R}

i.e. `◯` transmits polarity, like `∧` and `∨` and unlike `⊃`.  This is
forced: `◯` is monotone in its argument, so an occurrence of `A` inside
`◯A` has the polarity of the `◯A` occurrence itself.  It is recorded as
an extension because the paper's language has no `◯`, not because there
is a choice to make.

We compute the two sets simultaneously.  `sfPos A` is the pair
`(right-subformulas, left-subformulas)` generated by `A` occurring in
RIGHT position, and `sfNeg A` the pair generated by `A` in LEFT position;
then `Sf^R(G) = (sfPos G).1` and `Sf^L(G) = (sfPos G).2`. -/

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
    | .circ A =>
        ((Form.circ A) :: (sfPos A).1, (sfPos A).2)

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
    | .circ A =>
        ((sfNeg A).1, (Form.circ A) :: (sfNeg A).2)
end

/-- `Sf^R(G)`, the right (positive) subformulas of `G`. -/
def sfR (G : Form) : List Form := (sfPos G).1

/-- `Sf^L(G)`, the left (negative) subformulas of `G`. -/
def sfL (G : Form) : List Form := (sfPos G).2

/-- The paper's defining clauses, plus the `◯` clause, as a property of a
pair `(R, L)` standing for `(Sf^R(G), Sf^L(G))`.  Proving this of the
computed sets is the fidelity check on `sfR`/`sfL`. -/
structure SfClosed (R L : List Form) : Prop where
  rAnd : ∀ {A B : Form}, Form.and A B ∈ R → A ∈ R ∧ B ∈ R
  rOr : ∀ {A B : Form}, Form.or A B ∈ R → A ∈ R ∧ B ∈ R
  rImp : ∀ {A B : Form}, Form.imp A B ∈ R → A ∈ L ∧ B ∈ R
  rCirc : ∀ {A : Form}, Form.circ A ∈ R → A ∈ R
  lAnd : ∀ {A B : Form}, Form.and A B ∈ L → A ∈ L ∧ B ∈ L
  lOr : ∀ {A B : Form}, Form.or A B ∈ L → A ∈ L ∧ B ∈ L
  lImp : ∀ {A B : Form}, Form.imp A B ∈ L → A ∈ R ∧ B ∈ L
  lCirc : ∀ {A : Form}, Form.circ A ∈ L → A ∈ L

theorem SfClosed.union {R₁ L₁ R₂ L₂ : List Form}
    (h₁ : SfClosed R₁ L₁) (h₂ : SfClosed R₂ L₂) :
    SfClosed (R₁ ++ R₂) (L₁ ++ L₂) where
  rAnd := by
    intro A B hm; rcases List.mem_append.mp hm with h | h
    · exact ⟨List.mem_append_left _ (h₁.rAnd h).1, List.mem_append_left _ (h₁.rAnd h).2⟩
    · exact ⟨List.mem_append_right _ (h₂.rAnd h).1, List.mem_append_right _ (h₂.rAnd h).2⟩
  rOr := by
    intro A B hm; rcases List.mem_append.mp hm with h | h
    · exact ⟨List.mem_append_left _ (h₁.rOr h).1, List.mem_append_left _ (h₁.rOr h).2⟩
    · exact ⟨List.mem_append_right _ (h₂.rOr h).1, List.mem_append_right _ (h₂.rOr h).2⟩
  rImp := by
    intro A B hm; rcases List.mem_append.mp hm with h | h
    · exact ⟨List.mem_append_left _ (h₁.rImp h).1, List.mem_append_left _ (h₁.rImp h).2⟩
    · exact ⟨List.mem_append_right _ (h₂.rImp h).1, List.mem_append_right _ (h₂.rImp h).2⟩
  rCirc := by
    intro A hm; rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_left _ (h₁.rCirc h)
    · exact List.mem_append_right _ (h₂.rCirc h)
  lAnd := by
    intro A B hm; rcases List.mem_append.mp hm with h | h
    · exact ⟨List.mem_append_left _ (h₁.lAnd h).1, List.mem_append_left _ (h₁.lAnd h).2⟩
    · exact ⟨List.mem_append_right _ (h₂.lAnd h).1, List.mem_append_right _ (h₂.lAnd h).2⟩
  lOr := by
    intro A B hm; rcases List.mem_append.mp hm with h | h
    · exact ⟨List.mem_append_left _ (h₁.lOr h).1, List.mem_append_left _ (h₁.lOr h).2⟩
    · exact ⟨List.mem_append_right _ (h₂.lOr h).1, List.mem_append_right _ (h₂.lOr h).2⟩
  lImp := by
    intro A B hm; rcases List.mem_append.mp hm with h | h
    · exact ⟨List.mem_append_left _ (h₁.lImp h).1, List.mem_append_left _ (h₁.lImp h).2⟩
    · exact ⟨List.mem_append_right _ (h₂.lImp h).1, List.mem_append_right _ (h₂.lImp h).2⟩
  lCirc := by
    intro A hm; rcases List.mem_append.mp hm with h | h
    · exact List.mem_append_left _ (h₁.lCirc h)
    · exact List.mem_append_right _ (h₂.lCirc h)

/-- Inserting a formula into the RIGHT component preserves the clauses,
provided its own immediate components are already correctly placed. -/
theorem SfClosed.insertR {R L : List Form} {X : Form} (h : SfClosed R L)
    (hand : ∀ A B : Form, X = .and A B → A ∈ R ∧ B ∈ R)
    (hor : ∀ A B : Form, X = .or A B → A ∈ R ∧ B ∈ R)
    (himp : ∀ A B : Form, X = .imp A B → A ∈ L ∧ B ∈ R)
    (hcirc : ∀ A : Form, X = .circ A → A ∈ R) :
    SfClosed (X :: R) L where
  rAnd := by
    intro A B hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact ⟨List.mem_cons_of_mem _ (hand A B rfl).1,
             List.mem_cons_of_mem _ (hand A B rfl).2⟩
    · exact ⟨List.mem_cons_of_mem _ (h.rAnd h').1,
             List.mem_cons_of_mem _ (h.rAnd h').2⟩
  rOr := by
    intro A B hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact ⟨List.mem_cons_of_mem _ (hor A B rfl).1,
             List.mem_cons_of_mem _ (hor A B rfl).2⟩
    · exact ⟨List.mem_cons_of_mem _ (h.rOr h').1,
             List.mem_cons_of_mem _ (h.rOr h').2⟩
  rImp := by
    intro A B hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact ⟨(himp A B rfl).1, List.mem_cons_of_mem _ (himp A B rfl).2⟩
    · exact ⟨(h.rImp h').1, List.mem_cons_of_mem _ (h.rImp h').2⟩
  rCirc := by
    intro A hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact List.mem_cons_of_mem _ (hcirc A rfl)
    · exact List.mem_cons_of_mem _ (h.rCirc h')
  lAnd := fun hm => h.lAnd hm
  lOr := fun hm => h.lOr hm
  lImp := fun hm => ⟨List.mem_cons_of_mem _ (h.lImp hm).1, (h.lImp hm).2⟩
  lCirc := fun hm => h.lCirc hm

/-- Inserting a formula into the LEFT component, dually. -/
theorem SfClosed.insertL {R L : List Form} {X : Form} (h : SfClosed R L)
    (hand : ∀ A B : Form, X = .and A B → A ∈ L ∧ B ∈ L)
    (hor : ∀ A B : Form, X = .or A B → A ∈ L ∧ B ∈ L)
    (himp : ∀ A B : Form, X = .imp A B → A ∈ R ∧ B ∈ L)
    (hcirc : ∀ A : Form, X = .circ A → A ∈ L) :
    SfClosed R (X :: L) where
  rAnd := fun hm => h.rAnd hm
  rOr := fun hm => h.rOr hm
  rImp := fun hm => ⟨List.mem_cons_of_mem _ (h.rImp hm).1, (h.rImp hm).2⟩
  rCirc := fun hm => h.rCirc hm
  lAnd := by
    intro A B hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact ⟨List.mem_cons_of_mem _ (hand A B rfl).1,
             List.mem_cons_of_mem _ (hand A B rfl).2⟩
    · exact ⟨List.mem_cons_of_mem _ (h.lAnd h').1,
             List.mem_cons_of_mem _ (h.lAnd h').2⟩
  lOr := by
    intro A B hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact ⟨List.mem_cons_of_mem _ (hor A B rfl).1,
             List.mem_cons_of_mem _ (hor A B rfl).2⟩
    · exact ⟨List.mem_cons_of_mem _ (h.lOr h').1,
             List.mem_cons_of_mem _ (h.lOr h').2⟩
  lImp := by
    intro A B hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact ⟨(himp A B rfl).1, List.mem_cons_of_mem _ (himp A B rfl).2⟩
    · exact ⟨(h.lImp h').1, List.mem_cons_of_mem _ (h.lImp h').2⟩
  lCirc := by
    intro A hm; rcases List.mem_cons.mp hm with rfl | h'
    · exact List.mem_cons_of_mem _ (hcirc A rfl)
    · exact List.mem_cons_of_mem _ (h.lCirc h')

theorem self_mem_sfPos (X : Form) : X ∈ (sfPos X).1 := by
  cases X <;> simp [sfPos]

theorem self_mem_sfNeg (X : Form) : X ∈ (sfNeg X).2 := by
  cases X <;> simp [sfNeg]

mutual
  theorem sfPos_closed (X : Form) : SfClosed (sfPos X).1 (sfPos X).2 := by
    cases X with
    | atom p => constructor <;> intros <;> simp_all [sfPos]
    | bot => constructor <;> intros <;> simp_all [sfPos]
    | and A B =>
        refine ((sfPos_closed A).union (sfPos_closed B)).insertR ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
          exact ⟨List.mem_append_left _ (self_mem_sfPos A),
                 List.mem_append_right _ (self_mem_sfPos B)⟩
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C heq; cases heq
    | or A B =>
        refine ((sfPos_closed A).union (sfPos_closed B)).insertR ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
        · intro C D heq; cases heq
          exact ⟨List.mem_append_left _ (self_mem_sfPos A),
                 List.mem_append_right _ (self_mem_sfPos B)⟩
        · intro C D heq; cases heq
        · intro C heq; cases heq
    | imp A B =>
        refine ((sfNeg_closed A).union (sfPos_closed B)).insertR ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C D heq; cases heq
          exact ⟨List.mem_append_left _ (self_mem_sfNeg A),
                 List.mem_append_right _ (self_mem_sfPos B)⟩
        · intro C heq; cases heq
    | circ A =>
        refine (sfPos_closed A).insertR ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C heq; cases heq; exact self_mem_sfPos A

  theorem sfNeg_closed (X : Form) : SfClosed (sfNeg X).1 (sfNeg X).2 := by
    cases X with
    | atom p => constructor <;> intros <;> simp_all [sfNeg]
    | bot => constructor <;> intros <;> simp_all [sfNeg]
    | and A B =>
        refine ((sfNeg_closed A).union (sfNeg_closed B)).insertL ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
          exact ⟨List.mem_append_left _ (self_mem_sfNeg A),
                 List.mem_append_right _ (self_mem_sfNeg B)⟩
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C heq; cases heq
    | or A B =>
        refine ((sfNeg_closed A).union (sfNeg_closed B)).insertL ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
        · intro C D heq; cases heq
          exact ⟨List.mem_append_left _ (self_mem_sfNeg A),
                 List.mem_append_right _ (self_mem_sfNeg B)⟩
        · intro C D heq; cases heq
        · intro C heq; cases heq
    | imp A B =>
        refine ((sfPos_closed A).union (sfNeg_closed B)).insertL ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C D heq; cases heq
          exact ⟨List.mem_append_left _ (self_mem_sfPos A),
                 List.mem_append_right _ (self_mem_sfNeg B)⟩
        · intro C heq; cases heq
    | circ A =>
        refine (sfNeg_closed A).insertL ?_ ?_ ?_ ?_
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C D heq; cases heq
        · intro C heq; cases heq; exact self_mem_sfNeg A
end

/-! The defining clauses, now as theorems about `sfR`/`sfL`. -/

theorem sfR_self (G : Form) : G ∈ sfR G := self_mem_sfPos G

theorem sfR_and {G A B : Form} (h : Form.and A B ∈ sfR G) :
    A ∈ sfR G ∧ B ∈ sfR G := (sfPos_closed G).rAnd h

theorem sfR_or {G A B : Form} (h : Form.or A B ∈ sfR G) :
    A ∈ sfR G ∧ B ∈ sfR G := (sfPos_closed G).rOr h

theorem sfR_imp {G A B : Form} (h : Form.imp A B ∈ sfR G) :
    A ∈ sfL G ∧ B ∈ sfR G := (sfPos_closed G).rImp h

theorem sfR_circ {G A : Form} (h : Form.circ A ∈ sfR G) : A ∈ sfR G :=
  (sfPos_closed G).rCirc h

theorem sfL_and {G A B : Form} (h : Form.and A B ∈ sfL G) :
    A ∈ sfL G ∧ B ∈ sfL G := (sfPos_closed G).lAnd h

theorem sfL_or {G A B : Form} (h : Form.or A B ∈ sfL G) :
    A ∈ sfL G ∧ B ∈ sfL G := (sfPos_closed G).lOr h

theorem sfL_imp {G A B : Form} (h : Form.imp A B ∈ sfL G) :
    A ∈ sfR G ∧ B ∈ sfL G := (sfPos_closed G).lImp h

theorem sfL_circ {G A : Form} (h : Form.circ A ∈ sfL G) : A ∈ sfL G :=
  (sfPos_closed G).lCirc h

/-! ## The zones `Ĝ_at`, `Ĝ_imp`, `Ĝ`

"`Ĝ_at = Sf^L(G) ∩ PV`, `Ĝ_imp = Sf^L(G) ∩ Fm⊃`, `Ĝ = Ĝ_at ∪ Ĝ_imp`."
Contexts of `FRJ(G)`-sequents are subsets of `Ĝ`; `Γ^at` and `Γ^⊃` are the
corresponding parts of a context. -/

/-- `Ĝ_at = Sf^L(G) ∩ PV`. -/
def gAt (G : Form) : List Form := (sfL G).filter Form.isPV

/-- `Ĝ_imp = Sf^L(G) ∩ Fm⊃`. -/
def gImp (G : Form) : List Form := (sfL G).filter Form.isImp

/-- `Ĝ = Ĝ_at ∪ Ĝ_imp`.  The paper's, unchanged: the `◯`-free rules put
nothing else in a context.  See the third-zone note below. -/
def gHat (G : Form) : List Form := gAt G ++ gImp G

/-- `Sf^L(G) ∩ {◯-formulas}`.  Ours, and unused by the `◯`-free layer:
vocabulary for W5. -/
def gCirc (G : Form) : List Form := (sfL G).filter Form.isCirc

/-- `Γ^at`. -/
def atPart (Γ : List Form) : List Form := Γ.filter Form.isPV

/-- `Γ^⊃`. -/
def impPart (Γ : List Form) : List Form := Γ.filter Form.isImp

/-- `Γ^◯`.  Ours; see the third-zone note. -/
def circPart (Γ : List Form) : List Form := Γ.filter Form.isCirc

@[simp] theorem mem_gAt {G X : Form} : X ∈ gAt G ↔ (X ∈ sfL G ∧ X.isPV = true) := by
  simp [gAt, List.mem_filter]

@[simp] theorem mem_gImp {G X : Form} : X ∈ gImp G ↔ (X ∈ sfL G ∧ X.isImp = true) := by
  simp [gImp, List.mem_filter]

@[simp] theorem mem_gCirc {G X : Form} : X ∈ gCirc G ↔ (X ∈ sfL G ∧ X.isCirc = true) := by
  simp [gCirc, List.mem_filter]

@[simp] theorem mem_atPart {Γ : List Form} {X : Form} :
    X ∈ atPart Γ ↔ (X ∈ Γ ∧ X.isPV = true) := by simp [atPart, List.mem_filter]

@[simp] theorem mem_impPart {Γ : List Form} {X : Form} :
    X ∈ impPart Γ ↔ (X ∈ Γ ∧ X.isImp = true) := by simp [impPart, List.mem_filter]

@[simp] theorem mem_circPart {Γ : List Form} {X : Form} :
    X ∈ circPart Γ ↔ (X ∈ Γ ∧ X.isCirc = true) := by simp [circPart, List.mem_filter]

theorem gAt_subset_gHat {G : Form} : gAt G ⊆ gHat G :=
  fun _ h => List.mem_append_left _ h
theorem gImp_subset_gHat {G : Form} : gImp G ⊆ gHat G :=
  fun _ h => List.mem_append_right _ h

/-- The split that the join rules rely on: over a context drawn from `Ĝ`,
`Γ = Γ^at ++ Γ^⊃` up to membership.  With `◯` in the language this is a
statement about `◯`-free contexts, and it is exactly the invariant that
the well-formedness lemma of W3 has to supply. -/
theorem atPart_union_impPart {G : Form} {Γ : List Form} (h : Γ ⊆ gHat G) :
    Γ ≐ (atPart Γ ++ impPart Γ) := by
  constructor
  · intro X hX
    have := h hX
    rcases List.mem_append.mp this with hx | hx
    · exact List.mem_append_left _ (mem_atPart.mpr ⟨hX, (mem_gAt.mp hx).2⟩)
    · exact List.mem_append_right _ (mem_impPart.mpr ⟨hX, (mem_gImp.mp hx).2⟩)
  · intro X hX
    rcases List.mem_append.mp hX with hx | hx
    · exact (mem_atPart.mp hx).1
    · exact (mem_impPart.mp hx).1

/-! ## The closure `Cl(Γ)`

"The *closure* of `Γ`, denoted by `Cl(Γ)`, is the smallest set containing
the formulas `X` defined by the following grammar:

    X ::= C | X ∧ X | A ∨ X | X ∨ A | A ⊃ X       (C ∈ Γ, A any formula)"

Transcribed verbatim.  **No `◯` clause is added.**  One is available —
`◯` is a monad unit, so `α ⊩ X` implies `α ⊩ ◯X` by reflexivity of `R_m`,
and (Cl1) would survive — but `Cl` occurs in the side conditions of `⊃∈`
and `⊃∉`, so extending it changes the *rules*, and rule statements are
W5 and are Matthew's.  The candidate is recorded in
`docs/frj-lax-plan.md` §7; nothing here depends on it. -/

/-- `Cl(Γ)`, as an inductive predicate reading the grammar. -/
inductive Clo (Γ : List Form) : Form → Prop
  | base {C : Form} : C ∈ Γ → Clo Γ C
  | and {X Y : Form} : Clo Γ X → Clo Γ Y → Clo Γ (.and X Y)
  | orR {A X : Form} : Clo Γ X → Clo Γ (.or A X)
  | orL {A X : Form} : Clo Γ X → Clo Γ (.or X A)
  | imp {A X : Form} : Clo Γ X → Clo Γ (.imp A X)

/-- (Cl3), first half: `Γ ⊆ Cl(Γ)`. -/
theorem clo_subset {Γ : List Form} {C : Form} (h : C ∈ Γ) : Clo Γ C := .base h

/-- (Cl4): `Γ₁ ⊆ Γ₂` implies `Cl(Γ₁) ⊆ Cl(Γ₂)`. -/
theorem clo_mono {Γ₁ Γ₂ : List Form} (hsub : Γ₁ ⊆ Γ₂) {X : Form}
    (h : Clo Γ₁ X) : Clo Γ₂ X := by
  induction h with
  | base hC => exact .base (hsub hC)
  | and _ _ ihX ihY => exact .and ihX ihY
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih

/-- (Cl5): `Cl(Γ) ∩ PV = Γ ∩ PV`.  Only the `base` clause can produce a
variable, so the closure adds none. -/
theorem clo_pv {Γ : List Form} {p : String} (h : Clo Γ (.atom p)) :
    Form.atom p ∈ Γ := by
  cases h with
  | base hC => exact hC

/-- (Cl6): `Γ₁ ⊆ Cl(Γ₂)` implies `Cl(Γ₁) ⊆ Cl(Γ₂)`; equivalently the
second half of (Cl3), `Cl(Cl(Γ)) = Cl(Γ)`. -/
theorem clo_trans {Γ Δ : List Form} (h : ∀ X ∈ Δ, Clo Γ X) {Y : Form}
    (hY : Clo Δ Y) : Clo Γ Y := by
  induction hY with
  | base hC => exact h _ hC
  | and _ _ ihX ihY => exact .and ihX ihY
  | orR _ ih => exact .orR ih
  | orL _ ih => exact .orL ih
  | imp _ ih => exact .imp ih

/-- (Cl2): `A ∈ Cl(Γ)` implies `A ∈ Cl(Γ ∩ Sf(A))`. -/
theorem clo_sf {Γ : List Form} : ∀ {A : Form}, Clo Γ A → Clo (cap Γ (sf A)) A := by
  intro A h
  induction h with
  | @base C hC => exact .base (mem_cap.mpr ⟨hC, self_mem_sf C⟩)
  | @and X Y _ _ ihX ihY =>
      refine .and (clo_mono ?_ ihX) (clo_mono ?_ ihY)
      · exact cap_mono (fun _ h => h) (fun Z hZ => by simp [sf]; exact Or.inr (Or.inl hZ))
      · exact cap_mono (fun _ h => h) (fun Z hZ => by simp [sf]; exact Or.inr (Or.inr hZ))
  | @orR A X _ ih =>
      exact .orR (clo_mono
        (cap_mono (fun _ h => h) (fun Z hZ => by simp [sf]; exact Or.inr (Or.inr hZ))) ih)
  | @orL A X _ ih =>
      exact .orL (clo_mono
        (cap_mono (fun _ h => h) (fun Z hZ => by simp [sf]; exact Or.inr (Or.inl hZ))) ih)
  | @imp A X _ ih =>
      exact .imp (clo_mono
        (cap_mono (fun _ h => h) (fun Z hZ => by simp [sf]; exact Or.inr (Or.inr hZ))) ih)

/-! ### `Cl` is decidable, and so is `≐`

The method the campaign follows asks for side conditions as **decidable
fields**, and `Cl` occurs in the side conditions of both implication
rules.  `Clo` is an inductive predicate, but only one clause can produce
each shape, so it is decided by structural recursion on the formula.  The
`◯` case reads `Clo Γ (◯X) ↔ ◯X ∈ Γ` exactly because `Cl` has no `◯`
clause. -/

/-- The decision procedure for `Cl(Γ)`, read off the grammar. -/
def cloB (Γ : List Form) : Form → Bool
  | .atom p => decide (Form.atom p ∈ Γ)
  | .bot => decide (Form.bot ∈ Γ)
  | .and X Y => decide (Form.and X Y ∈ Γ) || (cloB Γ X && cloB Γ Y)
  | .or X Y => decide (Form.or X Y ∈ Γ) || cloB Γ X || cloB Γ Y
  | .imp A X => decide (Form.imp A X ∈ Γ) || cloB Γ X
  | .circ X => decide (Form.circ X ∈ Γ)

theorem cloB_iff {Γ : List Form} : ∀ {X : Form}, cloB Γ X = true ↔ Clo Γ X := by
  intro X
  induction X with
  | atom p =>
      constructor
      · intro h; exact .base (of_decide_eq_true h)
      · intro h; cases h with | base hC => simpa [cloB] using hC
  | bot =>
      constructor
      · intro h; exact .base (of_decide_eq_true h)
      · intro h; cases h with | base hC => simpa [cloB] using hC
  | and X Y ihX ihY =>
      constructor
      · intro h
        simp only [cloB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with h | ⟨hX, hY⟩
        · exact .base h
        · exact .and (ihX.mp hX) (ihY.mp hY)
      · intro h
        cases h with
        | base hC => simp [cloB, hC]
        | and hX hY => simp [cloB, ihX.mpr hX, ihY.mpr hY]
  | or X Y ihX ihY =>
      constructor
      · intro h
        simp only [cloB, Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with (h | h) | h
        · exact .base h
        · exact .orL (ihX.mp h)
        · exact .orR (ihY.mp h)
      · intro h
        cases h with
        | base hC => simp [cloB, hC]
        | orR hY => simp [cloB, ihY.mpr hY]
        | orL hX => simp [cloB, ihX.mpr hX]
  | imp A X _ ihX =>
      constructor
      · intro h
        simp only [cloB, Bool.or_eq_true, decide_eq_true_eq] at h
        rcases h with h | h
        · exact .base h
        · exact .imp (ihX.mp h)
      · intro h
        cases h with
        | base hC => simp [cloB, hC]
        | imp hX => simp [cloB, ihX.mpr hX]
  | circ X _ =>
      constructor
      · intro h; exact .base (of_decide_eq_true (by simpa [cloB] using h))
      · intro h; cases h with | base hC => simpa [cloB] using hC

instance decClo (Γ : List Form) (X : Form) : Decidable (Clo Γ X) :=
  decidable_of_decidable_of_iff cloB_iff

instance decSubset (l m : List Form) : Decidable (l ⊆ m) :=
  decidable_of_decidable_of_iff (p := ∀ x ∈ l, x ∈ m)
    ⟨fun h _ hx => h _ hx, fun h _ hx => h hx⟩

instance decEqv (l m : List Form) : Decidable (l ≐ m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The third zone: a W5 finding, recorded here and not acted on

`FRJ(G)` partitions the left formulas that may appear in a context into
`Ĝ_at` (variables) and `Ĝ_imp` (implications), and that partition is
exhaustive for IPC because `Cl` absorbs `∧` and `∨` on the left: a
conjunction or disjunction is forced at a world exactly when its
components' membership makes it so, and the join rules never need to
carry it.

`◯` does not fit either zone, and it is not absorbed by `Cl` in the way
`∧` and `∨` are.  `α ⊩ X` does imply `α ⊩ ◯X`, so the "trivially forced"
direction is available; but `◯A` can be forced at `α` *without* `A` being
forced there, exactly as `A ⊃ B` can be forced without `B`.  That is what
makes `Ĝ_imp` a zone in the first place, and by the same argument `◯`
needs a third zone `Ĝ_◯` with its own analogue of the support condition
(J2).

So the W5 rule design is not "add a `◯` right-introduction rule": it is
`Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯` and a join rule with three zones.  `gCirc`,
`circPart` and `isCirc` above are that vocabulary, defined and unused.
Nothing is proposed; the statement is Matthew's. -/

/-! ## Axiom audit

`collectAxioms` is the only sound oracle, and these pins are
`#guard_msgs`-guarded so that a regression is a build failure and not a
discovery months later.  The budget set in `docs/frj-lax-plan.md` §3.2 is
`[propext, Quot.sound]` at worst; **`Classical.choice` is absent
throughout**, which is what keeps the completeness construction of W4 on
a path to an actual procedure. -/

/-- info: 'FRJLax.clo_subset' does not depend on any axioms -/
#guard_msgs in
#print axioms clo_subset

/-- info: 'FRJLax.clo_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms clo_mono

/-- info: 'FRJLax.clo_pv' does not depend on any axioms -/
#guard_msgs in
#print axioms clo_pv

/-- info: 'FRJLax.clo_trans' does not depend on any axioms -/
#guard_msgs in
#print axioms clo_trans

/-- info: 'FRJLax.mem_rm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_rm

/-- info: 'FRJLax.mem_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_cap

/-- info: 'FRJLax.sfPos_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sfPos_closed

/-- info: 'FRJLax.sfR_imp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sfR_imp

/-- info: 'FRJLax.sfR_circ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sfR_circ

/-- info: 'FRJLax.sfL_circ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sfL_circ

/-- info: 'FRJLax.atPart_union_impPart' depends on axioms: [propext] -/
#guard_msgs in
#print axioms atPart_union_impPart

/-- info: 'FRJLax.clo_sf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms clo_sf

/-- info: 'FRJLax.cloB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cloB_iff

/-- info: 'FRJLax.decClo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decClo

/-- info: 'FRJLax.decEqv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decEqv

/-- info: 'FRJLax.Form.size_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Form.size_pos

/-- info: 'FRJLax.size_le_of_mem_sf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms size_le_of_mem_sf

/-- info: 'FRJLax.size_lt_of_mem_sfm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms size_lt_of_mem_sfm

/-- info: 'FRJLax.sf_subset_sfm_impL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sf_subset_sfm_impL

/-- info: 'FRJLax.sf_subset_sfm_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sf_subset_sfm_circ

end FRJLax
