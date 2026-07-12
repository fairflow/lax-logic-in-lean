import LaxLogic.PLLTopTop
import LaxLogic.PLLDecide

/-!
# Running the mechanisation: the normaliser as a program, and a
derivability tactic

Lean has no separate extraction step: every `def` *is* the program, and
`#eval` runs it through the compiler.  The `Prop`/`Type` boundary plays
the role of Coq's extraction erasure — propositions (such as the
strong-normalisation certificate driving `Tm.normalize`'s
`termination_by`) vanish at runtime, so the compiled normaliser is
literally "iterate `Tm.step?` until `none`", with
`Tm.normalize_spec : Steps t t.normalize ∧ Nf t.normalize` as its
mechanised warranty.  This file adds the missing I/O — a compact
pretty-printer — plus build-time demos, and packages the verified
G4iLL decision procedure as a *sound* proof-construction tactic
`pll_g4` for concrete derivability claims (sound, **not complete**:
see `PLLG4Gap`).
-/

open PLLFormula

namespace PLLND

/-! ### Displaying proof terms -/

/-- de Bruijn index of a variable. -/
def Var.idx : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Var Γ φ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

/-- Compact λ-syntax for proof terms: de Bruijn variables `#n`,
`val`/`let val` for the `◯`-monad. -/
def Tm.pretty : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → String
  | _, _, .var v => s!"#{v.idx}"
  | _, _, .abort _ t => s!"abort {t.pretty}"
  | _, _, .lam b => s!"(λ. {b.pretty})"
  | _, _, .app f a => s!"({f.pretty} {a.pretty})"
  | _, _, .pair a b => s!"⟨{a.pretty}, {b.pretty}⟩"
  | _, _, .fst t => s!"{t.pretty}.1"
  | _, _, .snd t => s!"{t.pretty}.2"
  | _, _, .inl t => s!"(inl {t.pretty})"
  | _, _, .inr t => s!"(inr {t.pretty})"
  | _, _, .case t u v => s!"(case {t.pretty} of {u.pretty} | {v.pretty})"
  | _, _, .val t => s!"val {t.pretty}"
  | _, _, .bind t u => s!"(let val• := {t.pretty} in {u.pretty})"

/-! ### The normaliser, running

Build-time demos: `Tm.normalize` executed by `#eval`, verdicts pinned
by `#guard_msgs`. -/

private def A₀ : PLLFormula := prop "A"

-- β: (λ. #0) #0 ⟶ #0
/-- info: "#0" -/
#guard_msgs in
#eval (Tm.app (.lam (.var .here)) (.var .here) : Tm [A₀] A₀).normalize.pretty

-- ◯-monad β: let val• := val #0 in val #0 ⟶ val #0
/-- info: "val #0" -/
#guard_msgs in
#eval (Tm.bind (.val (.var .here)) (.val (.var .here))
  : Tm [A₀] A₀.somehow).normalize.pretty

-- let-assoc then β: let val• := (let val• := val #0 in val #0) in val #0
/-- info: "val #0" -/
#guard_msgs in
#eval (Tm.bind (.bind (.val (.var .here)) (.val (.var .here)))
    (.val (.var .here)) : Tm [A₀] A₀.somehow).normalize.pretty

-- a *neutral* bind is already normal: let val• := #0 in val #0
/-- info: "(let val• := #0 in val #0)" -/
#guard_msgs in
#eval (Tm.bind (.var .here) (.val (.var .here))
  : Tm [A₀.somehow] A₀.somehow).normalize.pretty

/-! ### A sound derivability tactic -/

/-- `pll_g4` — automation for concrete PLL derivability claims: runs the
*verified* G4iLL decision procedure (`PLLDecide`) as compiled code via
`native_decide`, then converts along the mechanised bridges
`G4.toSC`, `cutElimination`, `curry_howard`.  Closes goals of the forms

* `G4 Γ C`
* `SC Γ C`
* `Nonempty (LaxND Γ C)`
* `Nonempty (Tm Γ C)`

**Caveats.**  (1) *Sound, not complete*: G4iLL misses PLL-derivable
sequents (`PLLG4Gap.sc_but_not_G4`), so this tactic failing proves
nothing — e.g. it cannot close the derivable
`SC [◯((◯p→r)→◯p), ◯p→r] r`.  (2) A positive verdict trusts the
compiled evaluator (axiom `Lean.ofReduceBool`), like every
`native_decide`; for a kernel-only certificate write the derivation
term explicitly, as in `PLLG4Gap`. -/
macro "pll_g4" : tactic =>
  `(tactic| first
    | exact PLLND.curry_howard.mpr (PLLND.cutElimination.mpr
        (PLLND.G4.toSC (by native_decide)))
    | exact PLLND.cutElimination.mpr (PLLND.G4.toSC (by native_decide))
    | exact PLLND.G4.toSC (by native_decide)
    | native_decide)

-- ◯-unit, as a natural-deduction claim
example : Nonempty (LaxND [] (A₀.ifThen A₀.somehow)) := by pll_g4

-- ◯-multiplication, at the proof-term level
example : Nonempty (Tm [] (A₀.somehow.somehow.ifThen A₀.somehow)) := by
  pll_g4

-- Howe's duplication sequent, in the cut-free sequent calculus
example : SC [((prop "B").ifThen ((prop "A").somehow.ifThen (prop "C"))).ifThen
      (prop "A").somehow,
    (prop "A").somehow.ifThen (prop "C"), (prop "B").somehow] (prop "C") := by
  pll_g4

-- and a raw G4 goal
example : G4 [] (A₀.somehow.somehow.ifThen A₀.somehow) := by pll_g4

/-- A named specimen of a `pll_g4`-produced proof, for the axiom audit
below. -/
theorem unit_nd : Nonempty (LaxND [] (A₀.ifThen A₀.somehow)) := by
  pll_g4

/-! The trust base of a `pll_g4`-produced proof, pinned honestly: the
per-declaration `unit_nd._native.native_decide.ax_1_1` axiom marks the
compiled-evaluator step (Lean ≥4.31 synthesises one such axiom per
`native_decide` use, replacing the older shared `Lean.ofReduceBool`) —
contrast the kernel-only certificates of `PLLG4Gap`. -/

/--
info: 'PLLND.unit_nd' depends on axioms: [propext, Classical.choice, Quot.sound, unit_nd._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms unit_nd

end PLLND
