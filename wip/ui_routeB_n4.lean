/-
Route (B), node **N4**: N1/N3 forward restated INTERDERIVABLY, and N4 PROVED on
◯-free stations by transport from `LJFIPC.uniform_interpolation_IPC`.

Why the restatement.  `wip/ui_routeB_n4_lit.lean` REFUTES the literal form of
N1 (`EStabEq`, `AStabEq`) at every saturated parked ◯-free station carrying a
parked compound implication: `interpP`'s attack row guards at the FULL station,
so at the antecedent's own goal the aggregate contains itself one fuel down and
the chains are strictly `sizeNeg`-ascending.  N3 forward as stated
(`hasUI_of_stabEq`) therefore has no applicable instance.  The interderivable
forms `EStabilises`/`AStabilises` survive; this file makes N3 forward consume
them, which needs `cutInv` (`LJF/OPolInv.lean`, PROVED 2026-09-06).

Contents:

* **Stage 2** `hasUI_of_stabilises` — N3 forward over the interderivable
  chains.  `cutInv` enters four times: once to bring `E_e` down to `E_{f₀}` in
  `minE`, three times in `minA` (bring `E_e` down, compose `A_k` with the
  stabilisation, discharge the residual `E_k`).
* **Stage 4** the ◯-free instance, by TRANSPORT.  Uniform interpolation for IPC
  is PROVED in this repository (`LJFIPC.uniform_interpolation_IPC`,
  `LJF/Complete.lean`), unconditional, at `[propext, Classical.choice,
  Quot.sound]`, with the ∀p half E-relativised — the shape of `IsUIPair.minA`.
  For a ◯-free station and goal the Pitts pair is
  `E := negOfO (∃p ⌊done⌋)`, `A := negOfO (∀p (⌊done⌋ ⇒ ⌊G⌋))`; soundness and
  minimality cross by `Inv.sound` one way and `polInvT`/`polInvL` the other.
* **Stage 4b** `interpP_circFree`, and `n4_circFree`, the interderivable N4 on
  ◯-free stations.

**One restriction, and it is not an artefact.**  `IsUIPair.minE` quantifies
over p-free `Δ`, `ψ` that may CARRY `◯`.  The IPC theorem cannot supply that:
`exI_min` requires `isIPL` of the test formula, and `⌊ψ⌋ ⊢ erase ⌊ψ⌋` fails for
a `◯` under an antecedent.  A UI pair against ◯-carrying test data at a ◯-free
station IS uniform interpolation for PLL restricted to ◯-free cells, i.e. the
thing route (B) is being built to prove — not a corollary of Pitts's theorem.
So the pair proved here is `IsUIPairCF`, `IsUIPair` with `Δ`, `ψ` additionally
◯-free, and the backward direction is re-derived for it
(`stabilises_of_hasUICF`).  Every use inside `stabilises_of_hasUI` is at
`Δ`, `ψ` built from `interpP` at a ◯-free station, which `interpP_circFree`
certifies ◯-free, so nothing is lost for N4.

The judgment restriction Matthew anticipated is NOT needed: `minE` is proved at
EVERY judgment `j`.  At `j = .lax` a ◯-free goal is a shift (`laxImpEmpty`,
`laxAndEmpty` empty the other two, `CircFreeN` excludes the box), the erasure
lands on `◯⌊P⌋`, `LaxND.erased` brings it down to `⌊P⌋` (both context and goal
are `isIPL`, so `erase` is the identity on them), the IPC minimality applies,
and `polInvL` re-focalises.
-/
import wip.ui_routeB_n3_cut
import wip.ui_routeB_n4_lit
import LJF.Complete
import Meta.Audit

set_option autoImplicit false

namespace LJFO

open PLLND

/-! # Stage 2 · N3 forward over the INTERDERIVABLE chains

`EStabilises`/`AStabilises` give interderivability, not equality, so where
`hasUI_of_stabEq` rewrote it must now COMPOSE, and composition in LJF◯ is
`cutInv`.  The two independent fuels of `UpFrom2` are what makes the `minA`
case delicate: the cofinality instance is read at ∃p-fuel `k` and ∀p-fuel `k`,
and both have to be brought down — the ∃p side to `f₀` and the ∀p side to
`f₁` — before the pair's `A` is in hand. -/

/-- **N3, forward, interderivably.**  If both chains are eventually constant UP
TO INTERDERIVABILITY at a saturated parked station, their values at the
thresholds are a uniform-interpolant pair for the cell.

    SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
    EStabilises p done → AStabilises p done G → HasUI p done G
-/
noncomputable def hasUI_of_stabilises {p : String} {done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (he : EStabilises p done) (ha : AStabilises p done G) : HasUI p done G := by
  obtain ⟨f₀, hE⟩ := he
  obtain ⟨f₁, hA⟩ := ha
  refine ⟨interpP p f₀ [] done none, interpP p f₁ [] done (some G),
    { pfreeE := interpP_pfree p _ _ _ _
      pfreeA := interpP_pfree p _ _ _ _
      soundE := eSoundP p f₀ [] done
      soundA := aSoundP p f₁ [] done G
      minE := ?_
      minA := ?_ }⟩
  · -- `E_{f₀} ⊢ E_k` (stabilisation) composed with `E_k, Δ ⊢ⱼ ψ` (cofinality)
    intro Δ ψ hΔ hψ j d
    obtain ⟨n, hw⟩ := s2 done Δ ψ hsat hP hΔ hψ d
    have hd : Inv (interpP p (n + f₀) [] done none :: Δ) [] j ψ :=
      hw (n + f₀) (Nat.le_add_right _ _)
    have hstab : Inv [interpP p f₀ [] done none] [] .tru
        (interpP p (n + f₀) [] done none) :=
      (hE (n + f₀) (Nat.le_add_left _ _)).1
    exact cutInv _ _ _ _ _ hstab hd
  · -- `E_{f₀} ⊢ E_k`, `E_k, Δ ⊢ A_k` (cofinality), `E_k, A_k ⊢ A_{f₁}`
    intro Δ hΔ d
    obtain ⟨m, hw⟩ := a2 done Δ G hsat hP hΔ d
    -- the fuel above all three thresholds
    have hk : Inv (interpP p (m + f₀ + f₁) [] done none :: Δ) [] .tru
        (interpP p (m + f₀ + f₁) [] done (some (jGoal .tru G))) :=
      hw (m + f₀ + f₁) (m + f₀ + f₁) (by omega) (by omega)
    rw [jGoal_tru] at hk
    have hEk : Inv [interpP p f₀ [] done none] [] .tru
        (interpP p (m + f₀ + f₁) [] done none) := (hE (m + f₀ + f₁) (by omega)).1
    -- (1) `E_{f₀}, Δ ⊢ A_k`
    have d1 : Inv (interpP p f₀ [] done none :: Δ) [] .tru
        (interpP p (m + f₀ + f₁) [] done (some G)) :=
      cutInv _ _ _ _ _ hEk hk
    -- (2) `A_k, E_k ⊢ A_{f₁}`, from the ∀p stabilisation, permuted
    have d2 : Inv (interpP p (m + f₀ + f₁) [] done (some G) ::
        [interpP p (m + f₀ + f₁) [] done none]) [] .tru
        (interpP p f₁ [] done (some G)) :=
      (hA (m + f₀ + f₁) (by omega)).2.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    -- (3) cut `A_k`: `E_{f₀}, Δ, E_k ⊢ A_{f₁}`
    have d3 : Inv ((interpP p f₀ [] done none :: Δ) ++
        [interpP p (m + f₀ + f₁) [] done none]) [] .tru
        (interpP p f₁ [] done (some G)) := cutInv _ _ _ _ _ d1 d2
    -- (4) cut `E_k` away against the ∃p stabilisation, then contract
    have d4 : Inv (interpP p (m + f₀ + f₁) [] done none ::
        (interpP p f₀ [] done none :: Δ)) [] .tru
        (interpP p f₁ [] done (some G)) :=
      d3.wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact List.mem_cons_of_mem _ hZ
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    exact (cutInv _ _ _ _ _ hEk d4).wk (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil
      · exact hZ)

end LJFO

/-! ## Pins -/

#axioms_within LJFO.hasUI_of_stabilises [propext, Classical.choice, Quot.sound]
