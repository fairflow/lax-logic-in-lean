import wip.atomForce
import wip.envDesc

/-!
# The boxed floor branch: the traversal, shape by shape

PROGRESS §102 leaves the boxed row needing one thing: from the source's second
component — a universal table at a grown context with the boxed goal `◯q` — reach the
*goal-clause* disjunct at some grown context, since `AtomForce.boxGoal_remap` then
carries it back to `Γ`.

§103 records why the natural abstraction ("the ambient at any larger context follows
from the ambient") must not be used: it is the existential ascent, and it is refuted.
The grown ambient has to be obtained **shape by shape**, and §103's table says how.

This file does the traversal.  The recursion is on the **defect**; at fuel `0` every
component is `⊤` or `⊥` and the boxed disjunct explodes.

## Scope

A `∨`-free space (inherited from `itpA_atom_forces`) and an **atom** boxed goal `◯q`
with `q ≠ p` — the shape the recursion reaches when the space's γ-heads are atomic.
-/

open PLLFormula

namespace PLLND
namespace BoxSnd

open GoalDesc AtomForce EnvDesc

/-- Project a conjunct out of a derivable `andAll`. -/
theorem projAll {Δ l : List PLLFormula} {φ : PLLFormula}
    (d : G4c Δ (andAll l)) (h : φ ∈ l) : G4c Δ φ :=
  G4c.cut d (G4c.andAll_elim h (G4c.identity_mem (.head _)))

/-- The target of the traversal: the boxed goal clause at `Γ`. -/
abbrev tgtClause (p : String) (S : Finset PLLFormula) (f c : Nat)
    (Γ : List PLLFormula) (q : String) : PLLFormula :=
  ((itpE p S f c Γ).ifThen (itpA p S (f + 1) (c + 1) Γ (prop q))).somehow

/-! ## The ungated projections

For each ungated context shape, the ambient's own clause for that formula is the
grown ambient at the context the `itpA` disjunct grows to.  These are pure
projections out of `itpEcls`; each is stated separately so the induction below reads
as the mathematics rather than as guard bookkeeping. -/

/-- `A ∧ B ∈ Γ'`: the ambient's clause **is** the grown ambient. -/
theorem grown_and (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B : PLLFormula}
    (hF : A.and B ∈ Γ') (h1 : ¬(A ∈ Γ' ∧ B ∈ Γ'))
    (h2 : (A ∈ Γ' ∨ A ∈ S) ∧ (B ∈ Γ' ∨ B ∈ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A :: B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨A.and B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `(prop q') ⊃ B ∈ Γ'` with `prop q' ∈ Γ'`: the ambient's clause is the grown
ambient outright. -/
theorem grown_impAtom_pres (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {q' : String} {B : PLLFormula}
    (hF : (prop q').ifThen B ∈ Γ') (h1 : B ∉ Γ') (h2 : B ∈ S)
    (h3 : (prop q' : PLLFormula) ∈ Γ')
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(prop q').ifThen B, hF, ?_⟩
  simp only [if_neg h1, if_pos h2, if_pos h3]
  exact List.mem_singleton.mpr rfl

/-- `(A ∧ B) ⊃ D ∈ Γ'`: the ambient's clause is the grown ambient at the curried
context. -/
theorem grown_impAnd (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B D : PLLFormula}
    (hF : (A.and B).ifThen D ∈ Γ') (h1 : A.ifThen (B.ifThen D) ∉ Γ')
    (h2 : A.ifThen (B.ifThen D) ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A.ifThen (B.ifThen D) :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A.and B).ifThen D, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `(A ∨ B) ⊃ D ∈ Γ'`: the ambient's clause is the grown ambient at the split
context. -/
theorem grown_impOr (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {A B D : PLLFormula}
    (hF : (A.or B).ifThen D ∈ Γ')
    (h1 : ¬(A.ifThen D ∈ Γ' ∧ B.ifThen D ∈ Γ'))
    (h2 : (A.ifThen D ∈ Γ' ∨ A.ifThen D ∈ S) ∧
      (B.ifThen D ∈ Γ' ∨ B.ifThen D ∈ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ (itpE p S f (c + 2) (A.ifThen D :: B.ifThen D :: Γ')) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨(A.or B).ifThen D, hF, ?_⟩
  simp only [if_neg h1, if_pos h2]
  exact List.mem_singleton.mpr rfl

/-- `◯χ ∈ Γ'`: the ambient's clause is the grown ambient **under a `◯`** — which is
the form the `itpA` disjunct for `◯χ` can use, since that disjunct is boxed too. -/
theorem grown_box (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ' Δ : List PLLFormula} {χ : PLLFormula}
    (hF : χ.somehow ∈ Γ') (h1 : ¬(χ ∈ Γ' ∨ χ ∉ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ')) :
    G4c Δ ((itpE p S f (c + 2) (χ :: Γ')).somehow) := by
  rw [itpE_succ] at hamb
  refine projAll hamb ?_
  unfold itpEcls
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨χ.somehow, hF, ?_⟩
  simp only [if_neg h1]
  exact List.mem_singleton.mpr rfl

end BoxSnd
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.BoxSnd.grown_and' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.grown_and

/--
info: 'PLLND.BoxSnd.grown_box' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSnd.grown_box
