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
