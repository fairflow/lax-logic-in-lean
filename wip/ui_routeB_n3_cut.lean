/-
Route (B), N3 backward and N6 with the composition obligation DISCHARGED.

`wip/ui_routeB_n3.lean` states `CutInv` as an obligation and proves N3
backward (`stabilises_of_hasUI`) and the PLL transport (`pll_ui_of_ljfo`)
RELATIVE to it.  `LJF/OPolInv.lean` now proves it — route (a), polarisation
invariance, the case list of `docs/cutinv-cases.md` — so both results become
unconditional in `CutInv`.

Nothing in `wip/ui_routeB_n3.lean` is edited: the instances live here.

What remains between this file and `PLL_UI` is therefore TWO things, not
three: N4 — stabilisation at every saturated parked station, which `CellsFor`
inherits through N3 forward — and WP4's transfer of a pair from the saturated
station back to `[negOfO φ]`.  `CutInv` is off the list.
-/
import LJF.OPolInv
import wip.ui_routeB_n3

namespace LJFO

/-- `LJFO.cutInv` IS the obligation: the two types are definitionally
equal. -/
noncomputable def cutInvOb : CutInv := cutInv

/-- **N3, backward, unconditionally.**  From a uniform-interpolant pair, both
chains stabilise up to interderivability. -/
noncomputable def stabilises_of_hasUI' {p : String} {done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (h : HasUI p done G) : EStabilises p done × AStabilises p done G :=
  stabilises_of_hasUI cutInvOb s2 a2 hsat hP h

/-- **N6, unconditionally.**  Uniform interpolation for PLL, from the cells:

    (∀ p, CellsFor p) → PLL_UI
-/
noncomputable def pll_ui_of_ljfo' : (∀ p, CellsFor p) → PLL_UI :=
  pll_ui_of_ljfo cutInvOb

end LJFO

/-! ## Pins

Measured with `#axioms_within_pin`.  `Classical.choice` is inherited from
`LJFO.cutInv` — see `LJF/OPolInv.lean` §4b — and from nowhere else: the
`Nonempty`-valued content `LJFO.cutInvNE` pins at `[propext, Quot.sound]`. -/

#axioms_within LJFO.cutInvOb [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.stabilises_of_hasUI' [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pll_ui_of_ljfo' [propext, Classical.choice, Quot.sound]
