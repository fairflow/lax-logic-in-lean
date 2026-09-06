/-
Route (B), node **N4**, WP12b, **stage 4**: the route plumbed.

`docs/ui-ljfo-clause-table.md` §4.28(2) states the route:

> prove the loop-checked recursion sound and cofinal at the top level; with
> literal stabilisation, N3 forward for the loop-checked recursion gives
> `HasUI` at every saturated station, and N3 BACKWARD for `interpP`
> (`stabilises_of_hasUI′`) turns that into `StabilisationAllP`, hence
> `PLL_UI` through WP4.  `interpP` is never compared with the loop-checked
> recursion fuel by fuel.

Three of the four inputs are now PROVED for `interpR`:

* literal stabilisation at every station — `rStabLitE_uncond`,
  `rStabLitA_uncond` (`wip/ui_routeB_r_bound.lean`, stage 1);
* soundness at every state and every `seen` — `eSoundR`, `aSoundR`
  (`wip/ui_routeB_r_sound.lean`, stage 2);
* `p`-freeness — `interpR_pfree` (`wip/ui_routeB_r_def.lean`).

The fourth is COFINALITY, `SatE2R` / `SatA2R`, stated below verbatim as
`SatE2P` / `SatA2P` are (`LJF/OFuelPMin.lean` Part 5) with `interpP p e []
done g` replaced by `interpR p e [] done g []`.  It is OPEN, and is carried
as a typed parameter (rule 1: never a `sorry`).

Over it, this module proves

    hasUI_R  : SatE2R p → SatA2R p → Saturated done → ParkedCtxP done →
                 HasUI p done G
    stabilisationAllP_of_R
             : SatE2P p → SatA2P p → SatE2R p → SatA2R p → StabilisationAllP p
    pll_ui_R : (∀ p, SatE2P p) → (∀ p, SatA2P p) →
               (∀ p, SatE2R p) → (∀ p, SatA2R p) → PLL_UI

`hasUI_R` is `hasUI_of_stabEq` (`wip/ui_routeB_n3.lean`) with `interpP`
replaced by `interpR` throughout: literal stabilisation makes both
minimality clauses a REWRITE, so no cut is spent inside N3 forward, and the
pair exhibited for the cell is the pair of `interpR` values at the two
thresholds.  `interpP` re-enters only at N3 backward, where
`stabilises_of_hasUI′` turns the pair into `interpP`'s own interderivable
stabilisation — never fuel by fuel.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_sound
import wip.ui_routeB_r_bound
import wip.ui_routeB_n3_cut
import wip.ui_routeB_wp4
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · The cofinality statements for `interpR`

`LJF/OFuelPMin.lean` Part 5 verbatim, at `interpR … []`. -/

/-- **Minimality of `∃p` at a saturated station, for `interpR`**: the `∃p`
approximant of the pair-recording recursion, started at the empty record, is
cofinal for the `p`-free consequences of the station. -/
def SatE2R (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      UpFrom (fun e => Inv (interpR p e [] done none [] :: Δ) [] j ψ)

/-- **Minimality of `∀p` at a saturated station, for `interpR`**
(E-relativised, as `SatA2P`).  The `∃p` fuel `e` and the `∀p` fuel `f` are
independent. -/
def SatA2R (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
      UpFrom2 (fun e f => Inv (interpR p e [] done none [] :: Δ) [] .tru
        (interpR p f [] done (some (jGoal j G)) []))

/-! # Part 2 · N3 forward for the pair-recording recursion

`hasUI_of_stabEq` verbatim.  Literal stabilisation is unconditional here
(stage 1), so it is not a hypothesis; soundness is `eSoundR` / `aSoundR`
at the empty todo, where `[] ++ done` is `done`. -/

/-- **N3 forward, for `interpR`.**  At a saturated parked station the two
`interpR` values at their stabilisation thresholds are a uniform-interpolant
pair for the cell — over cofinality alone. -/
noncomputable def hasUI_R {p : String} {done : List Neg} {G : Neg}
    (r2 : SatE2R p) (ra2 : SatA2R p)
    (hsat : Saturated done) (hP : ParkedCtxP done) : HasUI p done G := by
  obtain ⟨f₀, hE⟩ := rStabLitE_uncond p done
  obtain ⟨f₁, hA⟩ := rStabLitA_uncond p done G
  refine ⟨interpR p f₀ [] done none [], interpR p f₁ [] done (some G) [],
    { pfreeE := interpR_pfree p _ _ _ _ _
      pfreeA := interpR_pfree p _ _ _ _ _
      soundE := eSoundR p f₀ [] done []
      soundA := aSoundR p f₁ [] done G []
      minE := ?_
      minA := ?_ }⟩
  · intro Δ ψ hΔ hψ j d
    obtain ⟨n, hw⟩ := r2 done Δ ψ hsat hP hΔ hψ d
    have hd : Inv (interpR p (n + f₀) [] done none [] :: Δ) [] j ψ :=
      hw (n + f₀) (Nat.le_add_right _ _)
    rw [hE (n + f₀) (Nat.le_add_left _ _)] at hd
    exact hd
  · intro Δ hΔ d
    obtain ⟨n, hw⟩ := ra2 done Δ G hsat hP hΔ d
    have hd : Inv (interpR p (n + f₀ + f₁) [] done none [] :: Δ) [] .tru
        (interpR p (n + f₀ + f₁) [] done (some (jGoal .tru G)) []) :=
      hw (n + f₀ + f₁) (n + f₀ + f₁) (by omega) (by omega)
    rw [jGoal_tru] at hd
    rw [hE (n + f₀ + f₁) (by omega), hA (n + f₀ + f₁) (by omega)] at hd
    exact hd

/-! # Part 3 · Back to `interpP`, and to `PLL_UI` -/

/-- **N4 for `interpP`, through the pair-recording recursion.**  The pair
built from `interpR` is turned into `interpP`'s own interderivable
stabilisation by N3 BACKWARD — the two recursions are never compared fuel by
fuel. -/
noncomputable def stabilisationAllP_of_R {p : String}
    (s2 : SatE2P p) (a2 : SatA2P p) (r2 : SatE2R p) (ra2 : SatA2R p) :
    StabilisationAllP p :=
  fun done G hsat hP => stabilises_of_hasUI' s2 a2 hsat hP (hasUI_R r2 ra2 hsat hP)

/-- **Uniform interpolation for PLL through the pair-recording recursion**,
over the four cofinality statements as variables:

    (∀ p, SatE2P p) → (∀ p, SatA2P p) → (∀ p, SatE2R p) → (∀ p, SatA2R p)
      → PLL_UI
-/
noncomputable def pll_ui_R (s2 : ∀ p, SatE2P p) (a2 : ∀ p, SatA2P p)
    (r2 : ∀ p, SatE2R p) (ra2 : ∀ p, SatA2R p) : PLL_UI :=
  pll_ui_of_stabilisationAll s2 a2
    (fun p => stabilisationAllP_of_R (s2 p) (a2 p) (r2 p) (ra2 p))

/-! # Part 4 · The gate: literal stabilisation is not vacuous

`hasUI_R` reads the pair off `interpR` at the two thresholds delivered by
`rStabLitE_uncond` / `rStabLitA_uncond`.  Those thresholds are real: at the
◯-free cell (i) the `∀p` chain still MOVES between fuels 3 and 4, so a
stabilisation claim one fuel below the measured threshold would be false —
kernel-checked `= false` — while the chain is constant from 4 on. -/

/-- **GATE, watched failing**: the `∀p` chain at cell (i) is NOT constant one
fuel below its measured threshold. -/
theorem gate_r_ui_threshold :
    decide (interpR "p" 3 [] cell1 (some goal1) [] = interpR "p" 4 [] cell1 (some goal1) [])
      = false := by
  decide +kernel

/-- **CONTROL**: from the threshold on it is constant. -/
theorem gate_r_ui_control :
    decide (interpR "p" 4 [] cell1 (some goal1) [] = interpR "p" 5 [] cell1 (some goal1) [])
      = true ∧
    decide (interpR "p" 5 [] cell1 (some goal1) [] = interpR "p" 6 [] cell1 (some goal1) [])
      = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end LJFO

/-! ## Pins -/

#axioms_within LJFO.hasUI_R [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.stabilisationAllP_of_R [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pll_ui_R [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.gate_r_ui_threshold [propext]
#axioms_within LJFO.gate_r_ui_control [propext]
