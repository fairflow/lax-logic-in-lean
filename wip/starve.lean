import LaxLogic.PLLG4UITrunc

/-!
# Starvation at the budget floor — first bricks of the `cascade_low_pos_box` campaign

Terminology, in standard language (translating the tower's internal
vocabulary): the *universal quantifier table* `itpA p S fuel b Γ C` is the
disjunction (`orAll`) of its clause lists; a state *(Γ, C, b)* is **starved**
when that clause list is empty, so the table is literally `⊥` (`orAll [] =
⊥`).  The budget-gated clause families — the goal clause of a `◯`-shaped
goal, the truncation disjunct, and the two `⊃`-family environment clauses —
all vanish at budget `b = 0`.

The countermodel battery of the July 8–12 session (`wip/refute4.lean`)
located the *unique* false point of the bare low-band descent at exactly
(`◯`-shaped goal, `b = 0`).  This file proves the syntactic half of that
boundary as theorems:

* `itpAgoal_obGoal_floor`, `itpAfull_obGoal_floor` — at the floor a
  `◯`-goal's table is its environment table alone (goal clause and
  truncation both gated off);
* `itpA_obGoal_floor` — the floor normal form of the table;
* `itpA_starve_floor` — **starvation collapse**: empty environment table
  at the floor gives `itpA = ⊥` *literally*.

These are the base facts of the starvation-collapse classification that
the kernel's own failure analysis names as step one of the unattempted
proof plan (`(defect, budget)`-lexicographic landing map over starved
states); the campaign continues from here.
-/

open PLLFormula

namespace PLLND

/-- At budget `0` a `◯`-shaped goal contributes no goal clause. -/
theorem itpAgoal_obGoal_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) :
    itpAgoal p S f 0 Γ (D.somehow) = [] := rfl

/-- At budget `0` the truncation disjunct is gated off, so the full table
of a `◯`-goal is its environment table. -/
theorem itpAfull_obGoal_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) :
    itpAfull p S f 0 Γ (D.somehow) = itpAenv p S f 0 Γ (D.somehow) := by
  show (itpAoth p S f 0 Γ (D.somehow) ++
      (if (itpAoth p S f 0 Γ (D.somehow)).isEmpty then [] else [])) =
    itpAenv p S f 0 Γ (D.somehow)
  rw [ite_self, List.append_nil]
  show itpAgoal p S f 0 Γ (D.somehow) ++ itpAenv p S f 0 Γ (D.somehow) =
    itpAenv p S f 0 Γ (D.somehow)
  rw [itpAgoal_obGoal_floor, List.nil_append]

/-- The floor normal form: at budget `0` the universal table of a `◯`-goal
is the disjunction of its environment clauses alone. -/
theorem itpA_obGoal_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula) :
    itpA p S (f + 1) 0 Γ (D.somehow) =
      orAll (itpAenv p S f 0 Γ (D.somehow)) := by
  rw [itpA_succ, itpAfull_obGoal_floor]

/-- **Starvation collapse at the floor**: an empty environment table makes
the universal quantifier table of a `◯`-goal at budget `0` literally `⊥`.
This pins, as a theorem, the exact boundary at which the low-band descent
fails — the countermodel battery's unique false point. -/
theorem itpA_starve_floor (p : String) (S : Finset PLLFormula) (f : Nat)
    (Γ : List PLLFormula) (D : PLLFormula)
    (h : itpAenv p S f 0 Γ (D.somehow) = []) :
    itpA p S (f + 1) 0 Γ (D.somehow) = falsePLL := by
  rw [itpA_obGoal_floor, h]
  rfl

end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.itpA_starve_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.itpA_starve_floor

/-! ## The starved-seal engine, and starvation beyond the floor -/

namespace PLLND

/-- Cons-weakening at `G4c`. -/
private theorem wk {Γ : List PLLFormula} {C : PLLFormula} (ψ : PLLFormula)
    (d : G4c Γ C) : G4c (ψ :: Γ) C := by
  obtain ⟨n, h⟩ := d; exact ⟨n, h.weaken ψ⟩

/-- **A starved seal closes.**  A boxed guarded implication whose value
slot is `⊥`, together with a derivable guard, yields *any* `◯`-conclusion:
open the box, fire the guard, explode.  This is the engine that dispatches
every sealed branch whose inner partner is starved. -/
theorem box_absurd {Δ : List PLLFormula} {X : PLLFormula} (W : PLLFormula)
    (dBox : G4c Δ ((X.ifThen falsePLL).somehow)) (dX : G4c Δ X) :
    G4c Δ W.somehow := by
  refine G4c.cut dBox (G4c.laxL (.head _) ?_)
  refine G4c.cut (wk _ (wk _ dX)) ?_
  exact G4c.cut (G4c.mp X falsePLL _) (G4c.botL (.head _))

/-- The eliminated atom's goal clause is empty at **every** budget. -/
theorem itpAgoal_elimAtom (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) : itpAgoal p S f b Γ (prop p) = [] := by
  simp [itpAgoal]

/-- **Eliminated-atom starvation, all budgets**: with an empty environment
table the universal quantifier at the eliminated atom collapses to `⊥` at
any budget, not only the floor. -/
theorem itpA_starve_elimAtom (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (h : itpAenv p S f b Γ (prop p) = []) :
    itpA p S (f + 1) b Γ (prop p) = falsePLL := by
  rw [itpA_succ]
  show orAll (itpAgoal p S f b Γ (prop p) ++ itpAenv p S f b Γ (prop p)) =
    falsePLL
  rw [itpAgoal_elimAtom, h]
  rfl

end PLLND
