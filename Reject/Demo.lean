/-
The ◯ rules in action: a refutation BUILT FORWARDS.

`⊬ ¬◯⊥`, derived as a construction term rather than found by search:

    solo(fallible)              -- the base constructor: one world, ⊥ holds
    ──────────────── addRoot, with S := "everything" (the root's
    addRoot solo D                Rm-cone is the fallible world)
    ──────────────── boxHolds:  the root forces ◯⊥
    root ⊩ ◯⊥
    ──────────────── the root is infallible by construction, so ⊥ fails
    root ⊮ ◯⊥ ⊃ ⊥
    ──────────────── not_laxND_of_root
    ⊬ ¬◯⊥

Compare `BiLax/Pipeline.lean`, which certified the same fact by
CHECKING a saturated branch.  Here the object is a term built by the
rules; nothing is searched and nothing fails.
-/
import Reject.Build

namespace Reject

open PLLND

/-- The base: one fallible world (`⊥` holds there). -/
def falW : ConstraintModel :=
  solo (fun _ => True) True (fun _ _ => True.intro)

/-- The step: a root below it, whose `Rm`-cone is that world. -/
def rootD : RootData falW where
  S _ := True
  S_up _ _ := True.intro
  At _ := False
  At_hered h := absurd h not_false

/-- The constructed model: an infallible root below a fallible world. -/
def M₁ : ConstraintModel := addRoot falW rootD

/-- By `boxHolds`: the root forces `◯⊥`. -/
theorem root_forces_boxBot : M₁.force none (.somehow .falsePLL) :=
  boxHolds rootD ⟨(), True.intro, True.intro⟩
    (fun a => ⟨a, True.intro, True.intro⟩)

/-- The root is infallible, so `⊥` fails there. -/
theorem root_refutes_bot : ¬ M₁.force none .falsePLL := fun h => h

/-- Hence the root refutes `¬◯⊥ = ◯⊥ ⊃ ⊥`. -/
theorem root_refutes_negBoxBot :
    ¬ M₁.force none (.ifThen (.somehow .falsePLL) .falsePLL) := by
  intro h
  exact root_refutes_bot (h none True.intro root_forces_boxBot)

/-- **`⊬ ¬◯⊥`, by construction.** -/
theorem not_derivable_negBoxBot :
    ¬ Nonempty (LaxND [] (.ifThen (.somehow .falsePLL) .falsePLL)) :=
  not_laxND_of_root (by simp) root_refutes_negBoxBot

/-! ### The ◯-refutation rules, exercised

`◯p` fails at the root of the same model: `p` holds nowhere, so
neither the root nor its `Rm`-cone forces it (`boxRefuteHere`). -/

def M₂ : ConstraintModel :=
  addRoot (solo (fun _ => False) False (fun h => absurd h not_false))
    { S := fun _ => True, S_up := fun _ _ => True.intro,
      At := fun _ => False, At_hered := fun h => absurd h not_false }

theorem root_refutes_boxP :
    ¬ M₂.force none (.somehow (.prop "p")) :=
  boxRefuteHere _ (fun h => h) (fun _ _ h => h)

/-- **`⊬ ◯p`.** -/
theorem not_derivable_boxP :
    ¬ Nonempty (LaxND [] (.somehow (.prop "p"))) :=
  not_laxND_of_root (by simp) root_refutes_boxP

/-! ## Pins -/

/--
info: 'Reject.not_derivable_negBoxBot' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivable_negBoxBot

/--
info: 'Reject.not_derivable_boxP' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivable_boxP

end Reject
