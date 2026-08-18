/-
# FRJ◯ — the first modal refutation, and the gap it found

The exemplar for the modal rules: a refutation of

    G = ◯p ⊃ p

which is not a theorem of PLL.  Building it is what found the gap
recorded in `docs/frjlax-modal-rules.md` §4.5.
-/
import FRJLax.Calculus
import FRJLax.Modal

namespace FRJLax
namespace CircCell

def p : Form := .atom "p"
/-- `G = ◯p ⊃ p`, not a theorem of PLL. -/
def G : Form := .imp (.circ p) p

/-! The zones.  Note what is NOT here: `⊥ ∉ Sf^R(G)`, so there is no
regular axiom other than the one at `p`, and `Ĝ_at = {p}` — the axiom at
`p` removes it.  **No derivable regular sequent of this goal has `p` in
its context.** -/

example : sfR G = [G, p] := by decide
example : sfL G = [.circ p, p] := by decide
example : gAt G = [p] := by decide
example : gImp G = [] := by decide
example : gCirc G = [.circ p] := by decide
example : gHat G ≐ [p, .circ p] := by decide

/-! ## The gap

`⋈^At,p` needs a promise premise `Δ ⇒ D` with `p ∈ Cl(Δ)` — the modal
witness of (J5).  By `clo_pv` that means `p ∈ Δ`, and `Δ ⊆ Ĝ`, so `Δ`
would have to be a derivable regular context containing `p`.  There is
none: the only prime formula in `Sf^R(G)` is `p` itself, and both axioms
at `p` delete it.

Semantically the reason is sharper.  The countermodel needs a world
forcing `p`; at such a world `◯p` holds by the unit, hence `G` holds, and
`⊥ ∉ Sf^R(G)`.  So that world refutes **nothing** in `Sf^R(G)` — and every
world of `Mod(D)` is a p-sequent, which by construction refutes its own
goal.  The witness is therefore not a p-sequent at all.

## The repair

It is a FALLIBLE world.  Fallible worlds force everything and refute
nothing, so they are exactly the worlds that are not p-sequents.  `⋈^At,⊥`
declares the new world's modal successor to be one. -/

/-- The single irregular premise: `Ax^→` at `p` gives `· ; ◯p → p`, since
`Ĝ_at \ {p} = ∅` and `Ĝ_◯ = {◯p}`. -/
def ax : FRJi G [] [.circ p] p :=
  .axI (by decide) (by decide) (by decide) (by decide)

/-- The join keeps exactly `◯p`: `Σ^at = Θ^at = Σ^⊃ = Θ^⊃ = ∅` and
`Θ^◯ = {◯p}`. -/
example : joinCtxAtP [⟨[], [.circ p], p⟩] p = [.circ p] := by decide

/-- `◯p ⇒ p`, by `⋈^At,⊥`: the new world forces `◯p` through its fallible
modal successor and refutes `p`. -/
def step : FRJr G false [.circ p] p :=
  .joinAtF (.one ax) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- `◯p ⇒ ◯p ⊃ p`, by `⊃∈` regular, since `◯p ∈ Cl({◯p})`. -/
def refute : FRJr G false [.circ p] G :=
  .impInR step (by decide) (by decide)

/-- `⊢_FRJ◯(G) G`: the first modal refutation, and it is data. -/
def refutation : Refutation G := ⟨false, [.circ p], refute⟩

theorem provable : Provable G := .intro refutation

/-! ## The semantic side, computed

The model the refutation describes: two worlds, the upper one fallible,
`R_m = R_i`.  The root forces `◯p` and refutes `p`, hence refutes `G`. -/

/-- Two worlds `lo < hi`, `hi` fallible. -/
inductive V2 where | lo | hi
  deriving DecidableEq, Repr

/-- The order on `V2`. -/
def le2' : V2 → V2 → Bool
  | .lo, _ => true
  | .hi, .hi => true
  | .hi, .lo => false

/-- The model with a fallible top. -/
abbrev fallTop : Model where
  W := V2
  elems := [.lo, .hi]
  complete := by intro w; cases w <;> simp
  decEq := inferInstance
  Ri := fun a b => le2' a b = true
  Rm := fun a b => le2' a b = true
  Fal := fun w => w = .hi
  V := fun w _ => w = .hi
  ri_refl := by intro a; cases a <;> rfl
  ri_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le2']
  ri_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all [le2']
  rm_refl := by intro a; cases a <;> rfl
  rm_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [le2']
  sub_mi := fun h => h
  root := .lo
  root_le := by intro a; cases a <;> rfl
  hered_F := by intro w v h hw; cases w <;> cases v <;> simp_all [le2']
  hered_V := by intro w v h s hw; cases w <;> cases v <;> simp_all [le2']
  full_F := by intro w h s; exact h
  decRi := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decRm := fun _ _ => inferInstanceAs (Decidable (_ = true))
  decFal := fun _ => inferInstanceAs (Decidable (_ = _))
  decV := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- The root forces `◯p`, refutes `p`, and so refutes `G = ◯p ⊃ p`. -/
example :
    fallTop.force .lo (.circ p) ∧ ¬ fallTop.force .lo p
    ∧ ¬ fallTop.force .lo G := by decide

/-- `G` is therefore not valid — the semantic statement the refutation is
supposed to certify. -/
theorem not_PLL_G : ¬ PLL G :=
  fun h => (by decide : ¬ fallTop.force fallTop.root G) (h fallTop)

/-! ## What is and is not established here

`refutation` and `not_PLL_G` are both proved, but they are **not yet
connected**: the theorem `⊢_FRJ◯(G) G ⟹ G ∉ PLL` is the soundness
theorem, and it is OPEN.  This file shows that the rules *can* build the
refutation and that the intended countermodel *is* a countermodel; it
does not show that every refutation yields one. -/

end CircCell
end FRJLax
