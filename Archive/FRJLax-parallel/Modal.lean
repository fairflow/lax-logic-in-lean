/-
# FRJ◯ — the semantics of `◯`, and the screen the modal rules must pass

W5, first half: **before any modal rule is written down**, the semantic
facts those rules would have to rest on are stated and proved, and the
cells that decide the design are computed in concrete models.

This is the counterexample mandate applied to a rule table that does not
exist yet.  `FRJO/`'s `worldOK` was refuted because its rule's semantic
obligation was never isolated; here each obligation is a named lemma,
and each is either PROVED or the design that needs it is dropped.

Imports: `FRJLax.Model` and nothing else.
-/
import FRJLax.Model

namespace FRJLax
namespace Model

variable (M : Model)

/-! ## The two facts every modal rule needs

    M,w ⊩ ◯A   iff   for every v with R_i w v there is u with
                     R_m v u and M,u ⊩ A

Read positively and negatively:

* to **force** `◯A` at `w` it is enough to have one modal witness at `w`
  itself and `◯A` forced at every world strictly above `w`;
* to **refute** `◯A` at `w` it is enough that no modal successor of `w`
  forces `A`.

The asymmetry with `⊃` is the whole content of the modal extension.  For
`A ⊃ B` the obligation at the new world is discharged NEGATIVELY — the
antecedent fails there, so the implication holds vacuously — which is why
FRJ's support condition (J2) only has to name `A` as some premise's right
formula.  For `◯A` the obligation at the new world is POSITIVE: a witness
must exist.  A modal rule therefore has to *supply* one, and that is the
new data a join must carry. -/

/-- **Modal introduction.**  A witness at `w`, plus `◯A` above `w`, force
`◯A` at `w`.  This is the obligation any rule that keeps `◯A` in the
conclusion of a join must discharge. -/
theorem circ_intro {w : M.W} {A : Form}
    (wit : ∃ u, M.Rm w u ∧ M.force u A)
    (above : ∀ v, M.Ri w v → v ≠ w → M.force v (.circ A)) :
    M.force w (.circ A) := by
  intro v hv
  by_cases hvw : v = w
  · subst hvw; exact wit
  · exact above v hv hvw v (M.ri_refl v)

/-- **Modal refutation.**  If no modal successor of `w` forces `A`, then
`◯A` fails at `w`.  This is the obligation a rule concluding a sequent
with `◯A` on the right must discharge. -/
theorem not_force_circ {w : M.W} {A : Form}
    (h : ∀ u, M.Rm w u → ¬ M.force u A) : ¬ M.force w (.circ A) := by
  intro hf
  obtain ⟨u, hmu, hu⟩ := hf w (M.ri_refl w)
  exact h u hmu hu

/-- The converse of `not_force_circ` at the world itself: forcing `◯A`
produces a witness at `w`. -/
theorem exists_witness {w : M.W} {A : Form} (h : M.force w (.circ A)) :
    ∃ u, M.Rm w u ∧ M.force u A := h w (M.ri_refl w)

/-- **The unit.**  `A` forces `◯A`, by reflexivity of `R_m`.  Hence no
world forces `A` and refutes `◯A`, so the sequent `A ⇒ ◯A` must be
underivable in any sound extension — a standing test cell. -/
theorem circ_of_force {w : M.W} {A : Form} (h : M.force w A) :
    M.force w (.circ A) :=
  fun v hv => ⟨v, M.rm_refl v, M.force_mono hv h⟩

/-- **A fallible witness must cover the whole cone.**

The first form of this lemma tried here was

    R_m w u  →  Fal u  →  M ⊩_w ◯A

and it is FALSE: `u` is a modal successor of `w`, and says nothing about
the modal successors of a world strictly above `w`.  Found by the screen
below before any rule was written.  What is true is the cone form: -/
theorem circ_of_fallible_cone {w : M.W} {A : Form}
    (h : ∀ v, M.Ri w v → ∃ u, M.Rm v u ∧ M.Fal u) : M.force w (.circ A) := by
  intro v hv
  obtain ⟨u, hmu, hu⟩ := h v hv
  exact ⟨u, hmu, M.force_of_fallible hu A⟩

/-- **Barrenness.**  Call a world *barren for `A`* when none of its modal
successors forces `A`.  A world with no proper modal successor is barren
for `A` exactly when it fails `A` — which is the semantic content of a
regular `◯`-introduction rule: from `Γ ⇒ A` at a world that declared no
promise, infer `Γ ⇒ ◯A`. -/
theorem not_force_circ_of_no_promise {w : M.W} {A : Form}
    (solo : ∀ u, M.Rm w u → u = w) (h : ¬ M.force w A) :
    ¬ M.force w (.circ A) :=
  M.not_force_circ (fun u hu hf => h (solo u hu ▸ hf))

/-- **Refutation descends.**  If `◯A` fails anywhere above `w` it fails at
`w`.  So a rule may refute `◯A` at a new world by pointing at any
successor that refutes it — no new machinery needed for that direction. -/
theorem not_force_circ_of_above {w v : M.W} {A : Form}
    (hv : M.Ri w v) (h : ¬ M.force v (.circ A)) : ¬ M.force w (.circ A) :=
  fun hf => h (M.force_mono hv hf)

end Model

/-! ## The screen: concrete models, computed

`Model.decForce` makes forcing a decision procedure, so the cells below
are settled by `decide` and not by argument. -/

namespace Screen

/-! The world types are bespoke enumerations rather than `Fin n`: `Core.lean`
has zero imports, so no `Fintype`, no order API, and every structure field
is discharged by case analysis.  What matters is that `Model.decForce`
then makes each cell below a `decide`. -/

/-- Two worlds, `lo ≤ hi`. -/
inductive W2 where | lo | hi
  deriving DecidableEq, Repr

/-- The order on `W2`, as a `Bool`. -/
def le2 : W2 → W2 → Bool
  | .lo, _ => true
  | .hi, .hi => true
  | .hi, .lo => false

/-- The two-world model `lo < hi`, with `p` true only at `hi`, no fallible
world, and `R_m = R_i`.  The smallest model separating `◯p` from `p`. -/
abbrev two : Model where
  W := W2
  elems := [.lo, .hi]
  complete := by intro w; cases w <;> simp
  decEq := inferInstance
  Ri := fun a b => le2 a b = true
  Rm := fun a b => le2 a b = true
  Fal := fun _ => False
  V := fun w s => w = .hi ∧ s = "p"
  ri_refl := by intro a; cases a <;> rfl
  ri_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le2]
  ri_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all [le2]
  rm_refl := by intro a; cases a <;> rfl
  rm_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le2]
  sub_mi := fun h => h
  root := .lo
  root_le := by intro a; cases a <;> rfl
  hered_F := fun _ h => h.elim
  hered_V := by intro w v h p hp; cases w <;> cases v <;> simp_all [le2]
  full_F := fun h => h.elim
  decRi := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decRm := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decFal := fun _ => inferInstanceAs (Decidable False)
  decV := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `p` fails at the root. -/
example : ¬ two.force .lo (.atom "p") := by decide

/-- `◯p` holds at the root: every world above has a modal successor
forcing `p`, namely `hi`. -/
example : two.force .lo (.circ (.atom "p")) := by decide

/-- **The cell that decides the design.**  `◯p ⇒ p` is semantically
refutable: a world forces `◯p` and fails `p`.  So the modal extension
must be able to build a world whose modal successor forces something the
world itself does not — a *selective* witness.  A rule that could witness
`◯` only by a fallible world could not produce this model. -/
example : two.force .lo (.circ (.atom "p")) ∧ ¬ two.force .lo (.atom "p") := by
  decide

/-- `◯⊥` fails everywhere in a model with no fallible world. -/
example : ¬ two.force .lo (.circ .bot) := by decide

/-- `◯◯p` holds where `◯p` does, as idempotence requires. -/
example : two.force .lo (.circ (.circ (.atom "p"))) := by decide

/-- `p ⇒ ◯p` is NOT refutable — anywhere, not just here.  This is
`Model.circ_of_force`, and it is the standing test cell for the unit. -/
theorem unit_cell (M : Model) (w : M.W) (A : Form) :
    M.force w A → M.force w (.circ A) := M.circ_of_force

/-! ### The branching cell: one promise is not enough

`◯(p ∨ q) ⊃ ◯p ∨ ◯q` is not a theorem of PLL, and refuting it needs two
worlds above the root with *different* modal witnesses.  So the modal
data a join carries cannot be one global promise: it is attached to the
world the join creates, and different branches carry different ones. -/

/-- Three worlds: a root `bot` below two incomparable worlds `l`, `r`. -/
inductive W3 where | bot | l | r
  deriving DecidableEq, Repr

/-- The order on `W3`. -/
def le3 : W3 → W3 → Bool
  | .bot, _ => true
  | .l, .l => true
  | .r, .r => true
  | _, _ => false

/-- Root `bot` with incomparable successors `l` and `r`; `p` at `l`, `q`
at `r`; `R_m = R_i`. -/
abbrev branch : Model where
  W := W3
  elems := [.bot, .l, .r]
  complete := by intro w; cases w <;> simp
  decEq := inferInstance
  Ri := fun a b => le3 a b = true
  Rm := fun a b => le3 a b = true
  Fal := fun _ => False
  V := fun w s => (w = .l ∧ s = "p") ∨ (w = .r ∧ s = "q")
  ri_refl := by intro a; cases a <;> rfl
  ri_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le3]
  ri_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all [le3]
  rm_refl := by intro a; cases a <;> rfl
  rm_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le3]
  sub_mi := fun h => h
  root := .bot
  root_le := by intro a; cases a <;> rfl
  hered_F := fun _ h => h.elim
  hered_V := by intro w v h p hp; cases w <;> cases v <;> simp_all [le3]
  full_F := fun h => h.elim
  decRi := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decRm := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decFal := fun _ => inferInstanceAs (Decidable False)
  decV := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- At the root, `◯(p ∨ q)` holds while both `◯p` and `◯q` fail: the
modal witness of `l` forces `p` and not `q`, and that of `r` the other
way.  So a single promise world per derivation cannot do; the witness is
per-world. -/
example :
    branch.force .bot (.circ (.or (.atom "p") (.atom "q")))
    ∧ ¬ branch.force .bot (.circ (.atom "p"))
    ∧ ¬ branch.force .bot (.circ (.atom "q")) := by decide

end Screen

/-! ## Axiom audit -/

/-- info: 'FRJLax.Model.circ_intro' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.circ_intro

/-- info: 'FRJLax.Model.not_force_circ' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.not_force_circ

/-- info: 'FRJLax.Model.circ_of_force' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.circ_of_force

/-- info: 'FRJLax.Model.circ_of_fallible_cone' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.circ_of_fallible_cone

/-- info: 'FRJLax.Model.not_force_circ_of_no_promise' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.not_force_circ_of_no_promise

/-- info: 'FRJLax.Model.not_force_circ_of_above' does not depend on any axioms -/
#guard_msgs in
#print axioms Model.not_force_circ_of_above

end FRJLax
