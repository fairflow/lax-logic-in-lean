/-
# The modality: semantics, obligations, and the screens

**W2, first half.**  Before any modal rule is written down, the semantic
facts such a rule would have to rest on are isolated and proved, and the
cells that decide the design are computed in concrete models.  This is the
counterexample mandate applied to a rule table that does not exist yet.

Everything here is about `Kripke` as `FRJ/Basic.lean` now defines it — the
modal accessibility relation and the modal clause of forcing added at W1.
No rule of `FRJ/Calculus.lean` mentions the modality, and nothing in this
file is consumed by the calculus; it exists to make the W2 design
discussion machine-checked rather than verbal.
-/
import FRJ.Basic

namespace FRJ
namespace Kripke

variable (K : Kripke)

/-! ## Where the semantic obligations live

The five facts a modal rule rests on are stated and proved in
`FRJ/Basic.lean`, next to `force` — `Kripke.circ_intro`,
`Kripke.not_force_circ`, `Kripke.not_force_circ_of_no_promise`,
`Kripke.not_force_circ_of_above` and `Kripke.circ_of_force`.  They moved
there at W3 because the soundness proof consumes one of them (`◯∈`), and
`FRJ/Sound.lean` does not import this file.  Their axiom pins are still
kept here, at the end. -/

end Kripke

/-! ## The screens

`Kripke.decForce` makes forcing a decision procedure, `◯`-clause included,
so every cell below is settled by `decide` rather than by argument. -/

namespace Screen

/-! ### Two worlds

The world types are bespoke enumerations: every structure field is
discharged by case analysis, and `decide` then does the rest. -/

/-- Two worlds, `lo ≤ hi`. -/
inductive W2 where | lo | hi
  deriving DecidableEq, Repr

/-- The order on `W2`, as a `Bool`. -/
def le2 : W2 → W2 → Bool
  | .lo, _ => true
  | .hi, .hi => true
  | .hi, .lo => false

/-- `lo < hi`, with `p` true only at `hi`, and `Rm = ≤`. -/
abbrev two : Kripke where
  W := W2
  elems := [.lo, .hi]
  complete := by intro w; cases w <;> simp
  decEq := inferInstance
  le := fun a b => le2 a b = true
  le_refl := by intro a; cases a <;> rfl
  le_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le2]
  le_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all [le2]
  Rm := fun a b => le2 a b = true
  rm_refl := by intro a; cases a <;> rfl
  rm_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le2]
  sub_mi := fun h => h
  root := .lo
  root_le := by intro a; cases a <;> rfl
  V := fun w s => w = .hi ∧ s = "p"
  V_mono := by intro w v h s hs; cases w <;> cases v <;> simp_all [le2]
  Fal := fun _ => False
  fal_mono := fun _ h => h
  fal_V := fun h => h.elim
  decLe := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decV := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
  decRm := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decFal := fun _ => isFalse (fun h => h)

/-- **Screen 1 — the witness must be SELECTIVE.**  A world forces `◯p` and
refutes `p`.  So a modal rule must be able to build a world whose modal
successor forces something the world itself does not; a rule that could
witness the modality only by a world forcing everything could not produce
this model. -/
example : two.force .lo (.circ (.atom "p")) ∧ ¬ two.force .lo (.atom "p") := by
  decide

/-- Both screen models are INFALLIBLE, so `⊥` is forced nowhere in them
and `◯⊥` is forced nowhere either.  Making `◯⊥` forceable is exactly what
a fallible world does, and it needs more than being on top — see
`FRJ/Fallible.lean`. -/
example : ¬ two.force .lo (.circ .bot) := by decide

/-- `◯◯p` holds where `◯p` does. -/
example : two.force .lo (.circ (.circ (.atom "p"))) := by decide

/-- **The unit cell.**  `A ⇒ ◯A` is not refutable anywhere — not just
here.  Any rule set that derives it is unsound. -/
theorem unit_cell (K : Kripke) (w : K.W) (A : Form) :
    K.force w A → K.force w (.circ A) := K.circ_of_force

/-! ### Three worlds, branching -/

/-- A root below two incomparable worlds. -/
inductive W3 where | bot | l | r
  deriving DecidableEq, Repr

/-- The order on `W3`. -/
def le3 : W3 → W3 → Bool
  | .bot, _ => true
  | .l, .l => true
  | .r, .r => true
  | _, _ => false

/-- Root `bot` with incomparable successors `l` and `r`; `p` at `l`, `q`
at `r`; `Rm = ≤`. -/
abbrev branch : Kripke where
  W := W3
  elems := [.bot, .l, .r]
  complete := by intro w; cases w <;> simp
  decEq := inferInstance
  le := fun a b => le3 a b = true
  le_refl := by intro a; cases a <;> rfl
  le_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le3]
  le_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all [le3]
  Rm := fun a b => le3 a b = true
  rm_refl := by intro a; cases a <;> rfl
  rm_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le3]
  sub_mi := fun h => h
  root := .bot
  root_le := by intro a; cases a <;> rfl
  V := fun w s => (w = .l ∧ s = "p") ∨ (w = .r ∧ s = "q")
  V_mono := by intro w v h s hs; cases w <;> cases v <;> simp_all [le3]
  Fal := fun _ => False
  fal_mono := fun _ h => h
  fal_V := fun h => h.elim
  decLe := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decV := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
  decRm := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decFal := fun _ => isFalse (fun h => h)

/-- **Screen 2 — the witness is PER-WORLD.**  At the root, `◯(p ∨ q)`
holds while both `◯p` and `◯q` fail: the modal witness of `l` forces `p`
and not `q`, and that of `r` the other way.  So the modal data a join
carries cannot be one promise fixed for the whole derivation; it belongs
to the world the join creates. -/
example :
    branch.force .bot (.circ (.or (.atom "p") (.atom "q")))
    ∧ ¬ branch.force .bot (.circ (.atom "p"))
    ∧ ¬ branch.force .bot (.circ (.atom "q")) := by decide

/-- The same model shows the modality does not distribute over disjunction
— the formula below is refuted at the root. -/
example : ¬ branch.force .bot
    (.imp (.circ (.or (.atom "p") (.atom "q")))
          (.or (.circ (.atom "p")) (.circ (.atom "q")))) := by decide

/-! ### Screen 3 — the witness cannot be an arbitrary context

The third screen is not a model but a REFUTATION of a design.  The
tempting way to supply a witness is to let a rule declare "there is a
world forcing `Δ`" for a context `Δ ⊆ Ĝ` of its choosing.  That is
precisely the design refuted in the abandoned first attempt at this
extension: its world predicate constrained a zone only by membership in
the universe, with no closure condition, and three kernel-checked cells
killed it —

    [⊥] ⊢ p        [p ∧ q] ⊢ p        [p, p ⊃ q] ⊢ q

each derivable in the natural-deduction system yet admitted by the
predicate.  The lesson, stated as the obligation such a rule would carry:
a declared context must be REALISABLE, and realisability is not
membership.

The two ways out are recorded in `docs/frj-modal-rules.md` §5.  Only one
of them needs no realisability condition at all, because it rests on a
world that forces everything by construction — and that route is the one
W3 took: `Kripke.falTop` in `FRJ/Fallible.lean`. -/

/-- Realisability, as the obligation a context-declaring rule would have
to discharge.  Stated here so that the W2 discussion has the statement;
nothing proves it, and that is the point. -/
def Realisable (Δ : List Form) : Prop :=
  ∃ (K : Kripke) (w : K.W), K.forces w Δ

/-- Realisability is not membership in the universe: the closure has to be
respected.  Here is the second of the three cells, as a statement about
`Realisable` rather than about any particular calculus. -/
theorem realisable_closed {Δ : List Form} {A B : Form}
    (h : Realisable Δ) (hmem : Form.and A B ∈ Δ) :
    ∃ (K : Kripke) (w : K.W), K.force w A ∧ K.force w B := by
  obtain ⟨K, w, hw⟩ := h
  exact ⟨K, w, (hw _ hmem).1, (hw _ hmem).2⟩

end Screen

/-! ## Axiom audit -/

/-- info: 'FRJ.Kripke.circ_intro' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.circ_intro

/-- info: 'FRJ.Kripke.not_force_circ' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.not_force_circ

/-- info: 'FRJ.Kripke.not_force_circ_of_no_promise' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.not_force_circ_of_no_promise

/-- info: 'FRJ.Kripke.not_force_circ_of_above' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.not_force_circ_of_above

/-- info: 'FRJ.Kripke.circ_of_force' does not depend on any axioms -/
#guard_msgs in
#print axioms Kripke.circ_of_force

end FRJ
