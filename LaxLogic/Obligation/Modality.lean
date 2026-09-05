/-
# The two lax modalities `◯∀` and `◯∃`, and the rules that combine them

This is the meta-level (Lean `Prop`) rendering of the abstraction/refinement
apparatus of

> M. Fairtlough, M. Mendler and X. Cheng, *Abstraction and refinement in higher
> order logic*, in R. J. Boulton and P. B. Jackson (eds), Theorem Proving in
> Higher Order Logics (TPHOLs 2001), LNCS 2152, 201–216, Springer 2001.

The paper works in Isabelle/HOL, where there are no proof terms, so a *constraint
λ-term* `p` has to be carried alongside an *abstract formula* `M` as a syntactic
pair `p : M`, and each abstract formula is assigned a **refinement type** `|M|`
(Fig. 3) giving the type of constraint it may carry. Lean's dependent type
theory already has the terms, so the whole apparatus collapses to something much
smaller: the refinement type `|M|` becomes an ordinary index type `γ`, the
constraint λ-term becomes a predicate on `γ`, and the abstract formula becomes
the family `z ↦ (z : M)`. Fig. 4's two modal clauses,

    (p : ◯∀M)  =  ∀ z :: |M|.  p z  ⊃  (z : M)
    (p : ◯∃M)  =  ∃ z :: |M|.  p z  ∧  (z : M)

are then literally the definitions of `LaxAll` and `LaxEx` below.

`◯∀` **weakens**: it says `M` holds wherever the constraint is met. It is the
reading used by the `postpone` tactic, where the constraint is an outstanding
proof obligation and `◯∀` is the promise "`M`, once you discharge this".
`◯∃` **strengthens**: it says `M` holds somewhere the constraint is met.

Nothing here is a port of the Isabelle development; the definitions were
reformulated for Lean and every rule is proved from scratch. The paper's
Theorem 1 (conservativity of the `p : M` extension over HOL) is *not* addressed:
it is a meta-theoretical result about a different base logic, deliberately left
for later work.

## What is proved here

* `laxAll_val`, `laxEx_val` — the unit, at Fig. 6's singleton constraint
  `val_Q(x) = λy. x = y`.
* `laxAll_pair`, `laxEx_pair` — the rule `◯∧` of the paper (p. 9), combining
  constraints on *independent* witnesses by `∧_◯(p,q) = λ(w,z). p w ∧ q z`.
* `laxAll_meet`, `laxEx_meet` — the same-witness form, which is what a proof
  obligation tracker actually uses.
* `laxAll_image`, `laxEx_image` — the rule `◯⊃` of the paper (p. 9), propagating
  a constraint through an implication by `⊃_◯(r,p) = λz. ∃m. p m ∧ z = r m`.
* `laxEx_sum`, `laxAll_sum` — disjunction. Fig. 3 fixes the witness type as a
  SUM, and the two modalities then behave differently: `◯∃` distributes over
  `∨`, while `◯∀` over the same constraint yields a CONJUNCTION.
* functoriality, constraint monotonicity, strength, and the collapse to the
  one-witness case `Debt C A = C → A`.

## Fig. 3, and what of it is covered

The refinement type `|M|` fixes, for each connective, the witness type its
constraint lives on. It is therefore a specification for this file: every row is
a determinate addition, not a design question.

    |P|     := α  if P :: α ⇒ 𝔹    |M₁ ∧ M₂| := |M₁| × |M₂|   -- `pair`      ✓
    |true|  := 1                    |M₁ ∨ M₂| := |M₁| + |M₂|   -- `sum`       ✓
    |false| := 1                    |M₁ ⊃ M₂| := |M₁| ⇒ |M₂|   -- elim only   ~
                                    |∀x::α.M| := α ⇒ |M|       --             ✗
                                    |∃x::α.M| := α × |M|       --             ✗
    |◯∃M| := |M| ⇒ 𝔹   |◯∀M| := |M| ⇒ 𝔹                       -- `Constraint` ✓

Note the last row: the constraint of a modal formula is a **predicate** on
witnesses, `|M| ⇒ 𝔹`, not an element of `|M|`. That is exactly `Constraint γ`
below. For every other connective the constraint is an element of the type
shown, which is why `image` takes an honest function `γ → δ` rather than a
relation.

Still missing, each with its witness type already dictated above: the units,
`⊃`-introduction (where the constraint is itself a function), `∀` and `∃`.
-/

universe u v w

namespace LaxLogic.Obligation

/-- A **constraint** on witnesses of type `γ`: what Fig. 2 of the paper calls a
constraint λ-term, at the level of what such a term denotes.

In the timing reading `γ` is a clock and a constraint is a lower bound on when a
signal is available; in the proof-obligation reading `γ` is trivial and a
constraint is simply an outstanding goal. -/
abbrev Constraint (γ : Type u) : Type u := γ → Prop

/-- An **abstract formula** over witnesses of type `γ`, presented as the family
`z ↦ (z : M)` of its refinements. The index type `γ` plays the role of the
paper's refinement type `|M|` (Fig. 3). -/
abbrev Refined (γ : Type u) : Type u := γ → Prop

/-- The **weakening** lax modality `◯∀`. Fig. 4 of Fairtlough–Mendler–Cheng:

    (p : ◯∀M)  =  ∀ z :: |M|.  p z  ⊃  (z : M)

Read it as: `M` holds at every witness satisfying the constraint `p`. This is
the modality a proof-obligation tracker wants, because it says exactly "`M`,
modulo `p`". -/
def LaxAll {γ : Type u} (p : Constraint γ) (M : Refined γ) : Prop :=
  ∀ z, p z → M z

/-- The **strengthening** lax modality `◯∃`, dual to `LaxAll`. Fig. 4 of
Fairtlough–Mendler–Cheng:

    (p : ◯∃M)  =  ∃ z :: |M|.  p z  ∧  (z : M)

Read it as: `M` holds at some witness satisfying the constraint `p`. -/
def LaxEx {γ : Type u} (p : Constraint γ) (M : Refined γ) : Prop :=
  ∃ z, p z ∧ M z

@[inherit_doc LaxAll]
notation:1000 "◯∀[" p "]" M:1000 => LaxAll p M

@[inherit_doc LaxEx]
notation:1000 "◯∃[" p "]" M:1000 => LaxEx p M

/-! ### Constraint formation

The three constraint constructors the paper's rules need. `val` is Fig. 6's
`val_Q`; `pair` is `∧_◯`; `image` is `⊃_◯`. `meet` is the same-witness variant
of `pair`, which the paper uses implicitly whenever two components share a
clock and which is the only one a single-witness obligation tracker needs. -/

/-- The singleton constraint at `x`, written `val_Q(x) = λy. x = y` in Fig. 6 of
the paper. It is the constraint carried by an *unconstrained* proof: the witness
is already known, so nothing is outstanding. -/
def val {γ : Type u} (x : γ) : Constraint γ := fun y => x = y

/-- Combine constraints on **independent** witnesses:
`∧_◯(p,q) = λ(w,z). p w ∧ q z` (paper, p. 9). This is the constraint carried by
a conjunction whose two halves were constrained separately. -/
def pair {γ : Type u} {δ : Type v} (p : Constraint γ) (q : Constraint δ) :
    Constraint (γ × δ) :=
  fun wz => p wz.1 ∧ q wz.2

/-- Combine constraints on a **shared** witness, by conjunction. This is the
combination a proof-obligation tracker performs: two outstanding obligations
become one, and neither is forgotten.

In the timing reading, where constraints are lower bounds on a shared clock,
conjunction is `max` — see `LaxLogic.Obligation.Timing.meet_lowerBound`. -/
def meet {γ : Type u} (p q : Constraint γ) : Constraint γ :=
  fun z => p z ∧ q z

/-- Propagate a constraint through an implication whose refinement part is `r`:
`⊃_◯(r,p) = λz. ∃m. p m ∧ z = r m` (paper, p. 9). It is the direct image of `p`
along `r`.

This is the rule that makes obligation tracking free: a constraint incurred deep
inside a derivation is carried, unchanged in content, through everything built
on top of it. -/
def image {γ : Type u} {δ : Type v} (r : γ → δ) (p : Constraint γ) :
    Constraint δ :=
  fun z => ∃ m, p m ∧ z = r m

/-- The order on constraints: `p ≤ q` when `p` is the **harder** demand. A proof
under `q` is therefore also a proof under `p`, so moving down this order is what
"making progress on an obligation" means. -/
def Stronger {γ : Type u} (p q : Constraint γ) : Prop := ∀ z, p z → q z

/-! ### The unit -/

/-- Unit for `◯∀`: a proof at a known witness is a proof modulo the singleton
constraint at that witness. -/
theorem laxAll_val {γ : Type u} {M : Refined γ} {x : γ} (h : M x) :
    ◯∀[val x] M := by
  intro z hz
  exact hz ▸ h

/-- Unit for `◯∃`. -/
theorem laxEx_val {γ : Type u} {M : Refined γ} {x : γ} (h : M x) :
    ◯∃[val x] M :=
  ⟨x, rfl, h⟩

/-- A constraint that is met everywhere adds nothing: `◯∀` over the trivially
true constraint is just the universally quantified statement. -/
theorem laxAll_trivial {γ : Type u} {M : Refined γ} :
    ◯∀[fun _ => True] M ↔ ∀ z, M z :=
  ⟨fun h z => h z trivial, fun h z _ => h z⟩

/-! ### `◯∧` — combining two constraints -/

/-- **The rule `◯∧` of the paper (p. 9)**, on independent witnesses:

    Γ ⊢ p : ◯_Q M      Γ ⊢ q : ◯_Q N
    ─────────────────────────────────
      Γ ⊢ ∧_◯(p,q) : ◯_Q (M ∧ N)

with `∧_◯(p,q) = λ(w,z). p w ∧ q z`. Here in the `◯∀` reading. -/
theorem laxAll_pair {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ}
    (hM : ◯∀[p] M) (hN : ◯∀[q] N) :
    ◯∀[pair p q] (fun wz : γ × δ => M wz.1 ∧ N wz.2) :=
  fun _ hz => ⟨hM _ hz.1, hN _ hz.2⟩

/-- The rule `◯∧` in the `◯∃` reading. That both readings validate it is why the
paper states it for a generic modality `◯_Q`. -/
theorem laxEx_pair {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ}
    (hM : ◯∃[p] M) (hN : ◯∃[q] N) :
    ◯∃[pair p q] (fun wz : γ × δ => M wz.1 ∧ N wz.2) := by
  obtain ⟨w, hw, hMw⟩ := hM
  obtain ⟨z, hz, hNz⟩ := hN
  exact ⟨(w, z), ⟨hw, hz⟩, hMw, hNz⟩

/-- `◯∧` on a **shared** witness: two obligations conjoin, and the conjunction
of the two claims follows. This is the form a proof-obligation tracker uses, and
the reason a partial proof with several holes yields exactly one residual. -/
theorem laxAll_meet {γ : Type u} {p q : Constraint γ} {M N : Refined γ}
    (hM : ◯∀[p] M) (hN : ◯∀[q] N) :
    ◯∀[meet p q] (fun z => M z ∧ N z) :=
  fun z hz => ⟨hM z hz.1, hN z hz.2⟩

/-- `◯∃` on a shared witness. Note the asymmetry with `laxAll_meet`: for `◯∃`
the two halves must be witnessed *at the same point*, so this takes a single
combined hypothesis rather than two independent ones. The paired form
`laxEx_pair` is the one that needs no such agreement. -/
theorem laxEx_meet {γ : Type u} {p q : Constraint γ} {M N : Refined γ}
    (h : ◯∃[meet p q] (fun z => M z ∧ N z)) :
    ◯∃[p] M ∧ ◯∃[q] N := by
  obtain ⟨z, ⟨hp, hq⟩, hM, hN⟩ := h
  exact ⟨⟨z, hp, hM⟩, ⟨z, hq, hN⟩⟩

/-! ### `◯∨` — disjunction

Fig. 3 sets `|M ∨ N| = |M| + |N|`, so a constraint for a disjunction lives on a
SUM of witness types. Given that, the two modalities part company, and the
asymmetry is the expected one: a sum is a coproduct, so `∃` over it splits into
a disjunction while `∀` over it becomes a conjunction. -/

/-- The constraint for a disjunction: `|M ∨ N| = |M| + |N|` (Fig. 3), with each
injection constrained by its own side. -/
def sum {γ : Type u} {δ : Type v} (p : Constraint γ) (q : Constraint δ) :
    Constraint (γ ⊕ δ) :=
  fun z => match z with | .inl w => p w | .inr v => q v

/-- The disjunction of two abstract formulas, as a family over `|M| + |N|`. -/
def either {γ : Type u} {δ : Type v} (M : Refined γ) (N : Refined δ) :
    Refined (γ ⊕ δ) :=
  fun z => match z with | .inl w => M w | .inr v => N v

/-- **`◯∃` distributes over disjunction**, in both directions. A constrained
witness for `M ∨ N` is precisely a constrained witness for one of them. -/
theorem laxEx_sum {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ} :
    ◯∃[sum p q] (either M N) ↔ (◯∃[p] M ∨ ◯∃[q] N) := by
  constructor
  · rintro ⟨z | z, hz, hM⟩
    · exact .inl ⟨z, hz, hM⟩
    · exact .inr ⟨z, hz, hM⟩
  · rintro (⟨w, hw, hM⟩ | ⟨v, hv, hN⟩)
    · exact ⟨.inl w, hw, hM⟩
    · exact ⟨.inr v, hv, hN⟩

/-- **`◯∀` over the same sum constraint is a conjunction.** Not a failure of the
disjunction rule but the `∀`/`Σ` duality: a universal over a coproduct is a
product. So `◯∀` has no distribution law over `∨` — which is what one should
expect of a weakening modality, and is worth knowing before looking for one. -/
theorem laxAll_sum {γ : Type u} {δ : Type v}
    {p : Constraint γ} {q : Constraint δ} {M : Refined γ} {N : Refined δ} :
    ◯∀[sum p q] (either M N) ↔ (◯∀[p] M ∧ ◯∀[q] N) := by
  constructor
  · intro h
    exact ⟨fun w hw => h (.inl w) hw, fun v hv => h (.inr v) hv⟩
  · rintro ⟨h₁, h₂⟩ (z | z) hz
    · exact h₁ z hz
    · exact h₂ z hz

/-- One-sided introduction: the constraint that admits only the left injection.
The `∨`-introduction rule, with the constraint recording which disjunct was
used. -/
def inl {γ : Type u} {δ : Type v} (p : Constraint γ) : Constraint (γ ⊕ δ) :=
  fun z => match z with | .inl w => p w | .inr _ => False

@[inherit_doc inl]
theorem laxEx_inl {γ : Type u} {δ : Type v}
    {p : Constraint γ} {M : Refined γ} {N : Refined δ} (h : ◯∃[p] M) :
    ◯∃[inl (δ := δ) p] (either M N) := by
  obtain ⟨w, hw, hM⟩ := h
  exact ⟨.inl w, hw, hM⟩

@[inherit_doc inl]
theorem laxAll_inl {γ : Type u} {δ : Type v}
    {p : Constraint γ} {M : Refined γ} {N : Refined δ} (h : ◯∀[p] M) :
    ◯∀[inl (δ := δ) p] (either M N) := by
  rintro (z | z) hz
  · exact h z hz
  · exact hz.elim

/-! ### `◯⊃` — propagating a constraint -/

/-- **The rule `◯⊃` of the paper (p. 9)**:

    Γ ⊢ p : ◯_Q M      Γ ⊢ r : M ⊃ N
    ─────────────────────────────────
        Γ ⊢ ⊃_◯(r,p) : ◯_Q N

with `⊃_◯(r,p) = λz. ∃m. p m ∧ z = r m`, the direct image of `p` along the
refinement part `r` of the implication. Here in the `◯∀` reading. -/
theorem laxAll_image {γ : Type u} {δ : Type v}
    {p : Constraint γ} {M : Refined γ} {N : Refined δ} {r : γ → δ}
    (hM : ◯∀[p] M) (hr : ∀ m, M m → N (r m)) :
    ◯∀[image r p] N := by
  rintro _ ⟨m, hm, rfl⟩
  exact hr m (hM m hm)

/-- The rule `◯⊃` in the `◯∃` reading. -/
theorem laxEx_image {γ : Type u} {δ : Type v}
    {p : Constraint γ} {M : Refined γ} {N : Refined δ} {r : γ → δ}
    (hM : ◯∃[p] M) (hr : ∀ m, M m → N (r m)) :
    ◯∃[image r p] N := by
  obtain ⟨m, hm, hMm⟩ := hM
  exact ⟨r m, ⟨m, hm, rfl⟩, hr m hMm⟩

/-- The special case of `◯⊃` at `r = id`: functoriality in the claim, at a fixed
constraint. This is the everyday form — the constraint is untouched while the
proof continues around it. -/
theorem laxAll_map {γ : Type u} {p : Constraint γ} {M N : Refined γ}
    (hM : ◯∀[p] M) (hr : ∀ z, M z → N z) :
    ◯∀[p] N :=
  fun z hz => hr z (hM z hz)

@[inherit_doc laxAll_map]
theorem laxEx_map {γ : Type u} {p : Constraint γ} {M N : Refined γ}
    (hM : ◯∃[p] M) (hr : ∀ z, M z → N z) :
    ◯∃[p] N := by
  obtain ⟨z, hz, hMz⟩ := hM
  exact ⟨z, hz, hr z hMz⟩

/-! ### Monotonicity in the constraint, and strength -/

/-- `◯∀` is **antitone** in the constraint: demanding more leaves less to prove.
Together with `Stronger` this is the order along which an obligation is
discharged. -/
theorem laxAll_mono {γ : Type u} {p q : Constraint γ} {M : Refined γ}
    (hpq : Stronger p q) (h : ◯∀[q] M) :
    ◯∀[p] M :=
  fun z hz => h z (hpq z hz)

/-- `◯∃` is **monotone** in the constraint, the opposite direction to
`laxAll_mono`. -/
theorem laxEx_mono {γ : Type u} {p q : Constraint γ} {M : Refined γ}
    (hpq : Stronger p q) (h : ◯∃[p] M) :
    ◯∃[q] M := by
  obtain ⟨z, hz, hMz⟩ := h
  exact ⟨z, hpq z hz, hMz⟩

/-- Strength: an unconditional fact can be pushed under the modality. This is
what makes `◯∀` a *strong* monad in the claim argument, and it is what lets a
tactic keep using the ambient context while an obligation is outstanding. -/
theorem laxAll_strength {γ : Type u} {A : Prop} {p : Constraint γ}
    {M : Refined γ} (hA : A) (h : ◯∀[p] M) :
    ◯∀[p] (fun z => A ∧ M z) :=
  fun z hz => ⟨hA, h z hz⟩

@[inherit_doc laxAll_strength]
theorem laxEx_strength {γ : Type u} {A : Prop} {p : Constraint γ}
    {M : Refined γ} (hA : A) (h : ◯∃[p] M) :
    ◯∃[p] (fun z => A ∧ M z) := by
  obtain ⟨z, hz, hMz⟩ := h
  exact ⟨z, hz, hA, hMz⟩

/-! ### The one-witness case

When there is nothing to witness — the constraint is simply a proposition that
must hold — the whole apparatus collapses to an implication. This is the case
the `postpone` tactic works in, and `Debt C A` is the type of a proof of `A`
that still owes `C`. -/

/-- `A` holds **modulo the outstanding obligation** `C`. The one-witness case of
`LaxAll`, and the type of every theorem the `postpone` tactic produces.

The point of the definition is what it is *not*: `Debt C A` asserts nothing
about `A`. A proof of it is a complete, axiom-free theorem about a weaker
statement, whereas a proof of `A` by `sorry` is a tainted theorem about `A`. -/
abbrev Debt (C A : Prop) : Prop := C → A

/-- `Debt` is exactly `◯∀` over a one-element witness type. -/
theorem debt_iff_laxAll (C A : Prop) :
    Debt C A ↔ ◯∀[fun _ : Unit => C] (fun _ : Unit => A) :=
  ⟨fun h _ hc => h hc, fun h hc => h () hc⟩

/-- Discharging the obligation yields the theorem outright. -/
theorem Debt.discharge {C A : Prop} (h : Debt C A) (hc : C) : A := h hc

/-- Obligations conjoin: the one-witness instance of `laxAll_meet`, and the law
that makes several holes in one proof collapse to a single residual. -/
theorem Debt.and {C D A B : Prop} (h₁ : Debt C A) (h₂ : Debt D B) :
    Debt (C ∧ D) (A ∧ B) :=
  fun h => ⟨h₁ h.1, h₂ h.2⟩

/-- An obligation propagates through the rest of the proof unchanged: the
one-witness instance of `laxAll_map`. -/
theorem Debt.imp {C A B : Prop} (h : Debt C A) (r : A → B) : Debt C B :=
  fun hc => r (h hc)

/-- Obligations compose across two independent attempts: one reduces `A` to `C`,
the other reduces `C` to `D`. A `sorry`-based hole cannot express this, because
it records no proposition to compose with. -/
theorem Debt.trans {D C A : Prop} (h₁ : Debt D C) (h₂ : Debt C A) : Debt D A :=
  fun hd => h₂ (h₁ hd)

/-- Strengthening the obligation is always allowed. The one-witness instance of
`laxAll_mono`. -/
theorem Debt.weaken {C D A : Prop} (hdc : D → C) (h : Debt C A) : Debt D A :=
  fun hd => h (hdc hd)

/-! ### Two degeneracies

Both of the following are provable, and both constrain any tool built on this
theory. They are stated here rather than discovered later. -/

/-- **The trivial hole.** Taking the goal as its own obligation is always
possible, and achieves nothing: this is precisely what `sorry` does, and it is a
fixed point of the whole calculus.

Consequently a tool that reports "obligation recorded" as progress is
measuring nothing. Any search driven by obligation size needs an independent
measure and a guard against this term. -/
theorem Debt.trivial (A : Prop) : Debt A A := fun a => a

/-- **The vacuity of unrestricted `◯`.** "There is *some* constraint under which
`A` holds" is true for every `A`, by taking the constraint to be `False`.

So a lax modality is only meaningful relative to a *class* of admissible
constraints. For Propositional Lax Logic that class is the standard constraints,
and completeness with respect to them is Theorem 6 of Fairtlough and Mendler's
solution to Curry's problem, machine-checked in this development at
`LaxLogic/PLLCtxCompleteness.lean`. -/
theorem debt_exists_vacuous (A : Prop) : ∃ C, Debt C A :=
  ⟨False, fun h => h.elim⟩

end LaxLogic.Obligation
