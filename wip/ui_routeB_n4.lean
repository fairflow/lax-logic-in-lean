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
* **Stage 4b** `interpP_circFreeN` — `interpP` preserves ◯-freeness — and
  `n4_circFree`, the interderivable N4 on ◯-free stations, UNCONDITIONAL over
  the two cofinality variables.

**One restriction, and it is not an artefact.**  `IsUIPair.minE` quantifies
over p-free `Δ`, `ψ` that may CARRY `◯`.  The IPC theorem cannot supply that:
`exI_min` requires `isIPL` of the test formula, and `⌊ψ⌋ ⊢ erase ⌊ψ⌋` fails for
a `◯` under an antecedent.  A UI pair against ◯-carrying test data at a ◯-free
station IS uniform interpolation for PLL restricted to ◯-free cells, i.e. the
thing route (B) is being built to prove — not a corollary of Pitts's theorem.
So the pair proved here is `IsUIPairCF`, `IsUIPair` with `Δ`, `ψ` additionally
◯-free, and the backward direction is re-derived for it
(`stabilises_of_hasUICF`).  Every use inside `stabilises_of_hasUI` is at
`Δ`, `ψ` built from `interpP` at a ◯-free station, which `interpP_circFreeN`
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
open LJFIPC (PFree)

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

/-! # Stage 4 · N4 on ◯-free stations, by transport from Pitts's theorem

Uniform interpolation for IPC is PROVED here (`LJF/Complete.lean`):

    uniform_interpolation_IPC (p) (Γ) (φ) (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hφ : isIPL φ)

with `exI p Γ`, `allI p Γ φ` `p`-free, `Γ ⊢ ∃pΓ`, `∀pΓφ, Γ ⊢ φ`, and both
minimalities against `p`-free IPL test data, the ∀p half E-relativised
(`exI p Γ :: Δ ⊢ allI p Γ φ`) — literally `IsUIPair.minA`'s shape.  The transport
is: ERASE the polarised derivation (`Inv.sound`), apply the IPC property,
RE-FOCALISE (`polInvT` at `tru`, `polInvL` at `lax`).  `polInvT` holds at EVERY
polarised context, not merely `negOfO`-images, so `done` need not be canonical.

## 4.1 The two erasure transfers, and the polarisation transfer -/

section Transfer

open LJFIPC (PFree)

mutual
/-- Erasing a ◯-free positive gives an IPL formula. -/
theorem isIPL_erasePos : ∀ {P : Pos}, CircFreeP P → isIPL (erasePos P)
  | .atom _, _ => trivial
  | .fls, _ => trivial
  | .or _ _, h => ⟨isIPL_erasePos h.1, isIPL_erasePos h.2⟩
  | .down _, h => isIPL_eraseNeg h

/-- Erasing a ◯-free negative gives an IPL formula. -/
theorem isIPL_eraseNeg : ∀ {N : Neg}, CircFreeN N → isIPL (eraseNeg N)
  | .up _, h => isIPL_erasePos h
  | .imp _ _, h => ⟨isIPL_erasePos h.1, isIPL_eraseNeg h.2⟩
  | .and _ _, h => ⟨isIPL_eraseNeg h.1, isIPL_eraseNeg h.2⟩
  | .circ _, h => absurd h (by simp [CircFreeN])
end

/-- A ◯-free context erases to IPL formulas. -/
theorem isIPL_eraseCtx {Γ : List Neg} (h : CircFreeCtx Γ) :
    ∀ χ ∈ eraseCtx Γ, isIPL χ := by
  intro χ hχ
  obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hχ
  exact isIPL_eraseNeg (h N hN)

mutual
/-- `p`-freeness survives erasure (positives). -/
theorem pfree_erasePos {p : String} :
    ∀ {P : Pos}, PFreeP p P → PFree p (erasePos P)
  | .atom _, h => h
  | .fls, _ => trivial
  | .or _ _, h => ⟨pfree_erasePos h.1, pfree_erasePos h.2⟩
  | .down _, h => pfree_eraseNeg h

/-- `p`-freeness survives erasure (negatives). -/
theorem pfree_eraseNeg {p : String} :
    ∀ {N : Neg}, PFreeN p N → PFree p (eraseNeg N)
  | .up _, h => pfree_erasePos h
  | .imp _ _, h => ⟨pfree_erasePos h.1, pfree_eraseNeg h.2⟩
  | .and _ _, h => ⟨pfree_eraseNeg h.1, pfree_eraseNeg h.2⟩
  | .circ _, h => pfree_erasePos h
end

theorem pfree_eraseCtx {p : String} {Γ : List Neg} (h : PFreeCtx p Γ) :
    ∀ χ ∈ eraseCtx Γ, PFree p χ := by
  intro χ hχ
  obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hχ
  exact pfree_eraseNeg (h N hN)

mutual
/-- `p`-freeness survives the positive polarisation. -/
theorem pfreeP_posOfO {p : String} :
    ∀ {φ : PLLFormula}, PFree p φ → PFreeP p (posOfO φ)
  | .prop _, h => h
  | .falsePLL, _ => trivial
  | .or _ _, h => ⟨pfreeP_posOfO h.1, pfreeP_posOfO h.2⟩
  | .and _ _, h => ⟨pfreeN_negOfO h.1, pfreeN_negOfO h.2⟩
  | .ifThen _ _, h => ⟨pfreeP_posOfO h.1, pfreeN_negOfO h.2⟩
  | .somehow χ, h => pfreeP_posOfO (φ := χ) h

/-- `p`-freeness survives the negative polarisation. -/
theorem pfreeN_negOfO {p : String} :
    ∀ {φ : PLLFormula}, PFree p φ → PFreeN p (negOfO φ)
  | .prop _, h => h
  | .falsePLL, _ => trivial
  | .or _ _, h => ⟨pfreeP_posOfO h.1, pfreeP_posOfO h.2⟩
  | .and _ _, h => ⟨pfreeN_negOfO h.1, pfreeN_negOfO h.2⟩
  | .ifThen _ _, h => ⟨pfreeP_posOfO h.1, pfreeN_negOfO h.2⟩
  | .somehow χ, h => pfreeP_posOfO (φ := χ) h
end

end Transfer

/-! ## 4.2 The ◯-restricted uniform-interpolant pair

`IsUIPair` with `Δ` and `ψ` additionally ◯-free.  See the header: the IPC
theorem cannot reach ◯-carrying test data, and a pair that could IS uniform
interpolation for PLL on ◯-free cells. -/

/-- `(E, A)` is a uniform-interpolant pair for `done ⇒ G` AGAINST ◯-FREE TEST
DATA.  Everything else is `IsUIPair` verbatim, `minE` at every judgment
included. -/
structure IsUIPairCF (p : String) (done : List Neg) (G : Neg) (E A : Neg) : Type where
  pfreeE : PFreeN p E
  pfreeA : PFreeN p A
  soundE : Inv done [] .tru E
  minE : ∀ (Δ : List Neg) (ψ : Neg), PFreeCtx p Δ → PFreeN p ψ →
    CircFreeCtx Δ → CircFreeN ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ → Inv (E :: Δ) [] j ψ
  soundA : Inv (A :: done) [] .tru G
  minA : ∀ (Δ : List Neg), PFreeCtx p Δ → CircFreeCtx Δ →
    Inv (done ++ Δ) [] .tru G → Inv (E :: Δ) [] .tru A

/-- The cell has a ◯-restricted uniform-interpolant pair. -/
def HasUICF (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ (E A : Neg), IsUIPairCF p done G E A

/-- An unrestricted pair is in particular a ◯-restricted one. -/
def IsUIPairCF.of_isUIPair {p : String} {done : List Neg} {G E A : Neg}
    (u : IsUIPair p done G E A) : IsUIPairCF p done G E A where
  pfreeE := u.pfreeE
  pfreeA := u.pfreeA
  soundE := u.soundE
  minE := fun Δ ψ hΔ hψ _ _ => u.minE Δ ψ hΔ hψ
  soundA := u.soundA
  minA := fun Δ hΔ _ => u.minA Δ hΔ

/-! ## 4.3 The transport

`E := negOfO (∃p ⌊done⌋)`, `A := negOfO (∀p (⌊done⌋ ⇒ ⌊G⌋))`. -/

/-- The ∃p half of the transported pair. -/
noncomputable def uiE (p : String) (done : List Neg) : Neg :=
  negOfO (LJFIPC.exI p (eraseCtx done))

/-- The ∀p half of the transported pair. -/
noncomputable def uiA (p : String) (done : List Neg) (G : Neg) : Neg :=
  negOfO (LJFIPC.allI p (eraseCtx done) (eraseNeg G))

/-- **N4's cell, on a ◯-free station: PROVED.**  Every ◯-free cell of LJF◯ has
a uniform-interpolant pair against ◯-free test data, by transport from
`LJFIPC.uniform_interpolation_IPC`.  Saturation and parking are NOT needed —
this is a fact about the cell, not about `interpP`. -/
noncomputable def hasUICF_circFree {p : String} {done : List Neg} {G : Neg}
    (hd : CircFreeCtx done) (hG : CircFreeN G) : HasUICF p done G := by
  have hΓ : ∀ ψ ∈ eraseCtx done, isIPL ψ := isIPL_eraseCtx hd
  have hφ : isIPL (eraseNeg G) := isIPL_eraseNeg hG
  obtain ⟨⟨hEp, hEs, hEm⟩, ⟨hAp, hAs, hAm⟩⟩ :=
    LJFIPC.uniform_interpolation_IPC p (eraseCtx done) (eraseNeg G) hΓ hφ
  refine ⟨uiE p done, uiA p done G,
    { pfreeE := pfreeN_negOfO hEp
      pfreeA := pfreeN_negOfO hAp
      soundE := ?soundE
      soundA := ?soundA
      minE := ?minE
      minA := ?minA }⟩
  case soundE => -- `done ⊢ ∃p ⌊done⌋`
    refine (polInvT done _ ?_).some
    rw [uiE, (erase_polarise _).2]
    exact hEs
  case soundA => -- `∀p(⌊done⌋ ⇒ ⌊G⌋), done ⊢ G`
    refine (polInvT _ G ?_).some
    simp only [eraseCtx, List.map_cons, uiA, (erase_polarise _).2]
    exact hAs
  case minE => -- minimality of `∃p`, at every judgment
    intro Δ ψ hΔ hψ hΔc hψc j d
    have hΔi : ∀ χ ∈ eraseCtx Δ, isIPL χ := isIPL_eraseCtx hΔc
    have hΔp : ∀ χ ∈ eraseCtx Δ, PFree p χ := pfree_eraseCtx hΔ
    have hctx : ∀ χ ∈ eraseCtx done ++ eraseCtx Δ, isIPL χ := by
      intro χ hχ
      rcases List.mem_append.mp hχ with hχ | hχ
      · exact hΓ χ hχ
      · exact hΔi χ hχ
    cases j with
    | tru =>
        have h0 := Inv.sound d
        simp only [List.map_nil, List.nil_append, eraseCtx_append, goal] at h0
        have hmin := hEm (eraseCtx Δ) (eraseNeg ψ) hΔi hΔp (isIPL_eraseNeg hψc)
          (pfree_eraseNeg hψ) ⟨h0⟩
        refine (polInvT _ ψ ?_).some
        simp only [eraseCtx, List.map_cons, uiE, (erase_polarise _).2]
        exact hmin
    | lax =>
        -- at `lax` only a SHIFT goal is inhabited (`laxImpEmpty`,
        -- `laxAndEmpty`), and `CircFreeN` excludes the box
        cases ψ with
        | imp Q N => exact (laxImpEmpty d).elim
        | and M N => exact (laxAndEmpty d).elim
        | circ P => simp only [CircFreeN] at hψc
        | up P =>
            have h0 := Inv.sound d
            simp only [List.map_nil, List.nil_append, eraseCtx_append, goal,
              eraseNeg] at h0
            -- `⌊done⌋, ⌊Δ⌋ ⊢ ◯⌊P⌋` and everything is IPL, so `LaxND.erased`
            -- brings the goal down to `⌊P⌋` and fixes the context
            have h1 := h0.erased
            rw [PLLND.map_erase_eq_self _ hctx,
              show PLLND.erase (PLLFormula.somehow (erasePos P))
                = PLLND.erase (erasePos P) from rfl,
              PLLND.erase_eq_self_of_isIPL _ (isIPL_erasePos hψc)] at h1
            have hmin := hEm (eraseCtx Δ) (erasePos P) hΔi hΔp
              (isIPL_erasePos hψc) (pfree_erasePos hψ) ⟨h1⟩
            refine (polInvL _ P ?_).some
            simp only [eraseCtx, List.map_cons, uiE, (erase_polarise _).2]
            exact Nonempty.map LaxND.laxIntro hmin
  case minA => -- minimality of `∀p`, E-relativised
    intro Δ hΔ hΔc d
    have hΔi : ∀ χ ∈ eraseCtx Δ, isIPL χ := isIPL_eraseCtx hΔc
    have hΔp : ∀ χ ∈ eraseCtx Δ, PFree p χ := pfree_eraseCtx hΔ
    have h0 := Inv.sound d
    simp only [List.map_nil, List.nil_append, eraseCtx_append, goal] at h0
    have hmin := hAm (eraseCtx Δ) hΔi hΔp ⟨h0⟩
    refine (polInvT _ _ ?_).some
    simp only [eraseCtx, List.map_cons, uiE, uiA, (erase_polarise _).2]
    exact hmin

/-! # Stage 4b · N4 on ◯-free stations, interderivably

`stabilises_of_hasUI` (`wip/ui_routeB_n3.lean`) tests the pair's minimality at
exactly two places, both built from `interpP` at the station itself:

    minE  at  Δ := [],  ψ := E_k = interpP p k [] done none
    minA  at  Δ := [A_k] = [interpP p k [] done (some G)]

so the ◯-restricted pair suffices PROVIDED `interpP` preserves ◯-freeness at a
◯-free station.  That is the one fact this stage needs and does not have. -/

/-- A goal slot is ◯-free (`none`, the `∃p` mode, vacuously). -/
def OptCircFree : Option Neg → Prop
  | none => True
  | some G => CircFreeN G

/-- `interpP` preserves ◯-freeness at a ◯-free station.  Stated as a named
predicate because `stabilises_of_hasUICF` consumes it twice; PROVED below
(`circFreeInterpP`), so nothing here is an obligation.

`interpP` writes a `circ` in exactly two places — the box row `◯↓E(↑Q :: rest)` of a parked `◯Q ∈ done`,
and the seven `◯`-goal aggregates — and both are unreachable when the station
and the goal are ◯-free.  Everything else it writes is `nAnd`, `nOrAll`,
`nAndAll`, `pGuard`, `atomHead` and sub-formulas of its inputs. -/
def CircFreeInterpP (p : String) : Prop :=
  ∀ (f : Nat) (done : List Neg) (g : Option Neg),
    CircFreeCtx done → OptCircFree g → CircFreeN (interpP p f [] done g)

/-- **N3 backward for the ◯-restricted pair.**  `stabilises_of_hasUI` verbatim,
with the two ◯-freeness side conditions discharged from `CircFreeInterpP`.
`cutInv` enters exactly where it does there. -/
noncomputable def stabilises_of_hasUICF {p : String} {done : List Neg} {G : Neg}
    (cf : CircFreeInterpP p) (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done) (hd : CircFreeCtx done)
    (hG : CircFreeN G) (h : HasUICF p done G) :
    EStabilises p done × AStabilises p done G := by
  obtain ⟨E, A, u⟩ := h
  have hEdone : Inv (done ++ []) [] .tru E :=
    u.soundE.wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ))
  obtain ⟨n, hv⟩ := s2 done [] E hsat hP pfreeCtx_nil u.pfreeE hEdone
  have hAdone : Inv (done ++ [A]) [] .tru G :=
    u.soundA.wk (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      · exact List.mem_append.mpr (Or.inl hZ))
  obtain ⟨m, hw⟩ := a2 done [A] G hsat hP (pfreeCtx_singleton u.pfreeA) hAdone
  -- `E ⊢ E_k`: the ∃p approximant is ◯-free, so the restricted `minE` applies
  have hEmin : ∀ k : Nat, Inv (E :: []) [] .tru (interpP p k [] done none) :=
    fun k => u.minE [] _ pfreeCtx_nil (interpP_pfree p _ _ _ _)
      (fun _ hZ => absurd hZ List.not_mem_nil) (cf k done none hd trivial)
      ((eSoundP p k [] done).wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ)))
  -- `E, A_k ⊢ A`: likewise, the ∀p approximant is ◯-free
  have hAmin : ∀ k : Nat, Inv (E :: [interpP p k [] done (some G)]) [] .tru A :=
    fun k => u.minA _ (pfreeCtx_singleton (interpP_pfree p _ _ _ _))
      (fun Z hZ => by
        rcases List.mem_singleton.mp hZ with rfl
        exact cf k done (some G) hd hG)
      ((aSoundP p k [] done G).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
        · exact List.mem_append.mpr (Or.inl hZ)))
  refine ⟨⟨n + m, fun f hf => ⟨?_, ?_⟩⟩, ⟨n + m, fun f hf => ⟨?_, ?_⟩⟩⟩
  · exact cutInv _ _ _ _ _ (hv (n + m) (by omega)) (hEmin f)
  · exact cutInv _ _ _ _ _ (hv f (by omega)) (hEmin (n + m))
  · have hEf : Inv (interpP p f [] done none :: []) [] .tru E := hv f (by omega)
    have hA : Inv ([interpP p f [] done none] ++
        [interpP p (n + m) [] done (some G)]) [] .tru A :=
      cutInv _ _ _ _ _ hEf (hAmin (n + m))
    have hcof : Inv (interpP p f [] done none :: [A]) [] .tru
        (interpP p f [] done (some (jGoal .tru G))) := hw f f (by omega) (by omega)
    rw [jGoal_tru] at hcof
    have hcof' : Inv (A :: [interpP p f [] done none]) [] .tru
        (interpP p f [] done (some G)) :=
      hcof.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    exact (cutInv _ _ _ _ _ hA hcof').wk (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hZ
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil)
  · have hEf : Inv (interpP p f [] done none :: []) [] .tru E := hv f (by omega)
    have hA : Inv ([interpP p f [] done none] ++ [interpP p f [] done (some G)])
        [] .tru A := cutInv _ _ _ _ _ hEf (hAmin f)
    have hcof : Inv (interpP p f [] done none :: [A]) [] .tru
        (interpP p (n + m) [] done (some (jGoal .tru G))) :=
      hw f (n + m) (by omega) (by omega)
    rw [jGoal_tru] at hcof
    have hcof' : Inv (A :: [interpP p f [] done none]) [] .tru
        (interpP p (n + m) [] done (some G)) :=
      hcof.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    exact (cutInv _ _ _ _ _ hA hcof').wk (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact hZ
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil)

/-! ## 4c · Discharging the obligation

The `circFree` counterparts of `LJF/OCore.lean`'s `pfree_*` family, then the
induction.  Two features make it shorter than `interpP_pfree`: the seven ◯-goal
aggregates and the two ◯-carrying processing clauses are UNREACHABLE under the
hypotheses, and the `circ` arm of every station-row match dies on
`CircFreeCtx done`. -/

section CircFreeInterp

theorem circFree_nTop : CircFreeN nTop := by simp [nTop, CircFreeN, CircFreeP]

theorem circFree_nBot : CircFreeN nBot := by simp [nBot, CircFreeN, CircFreeP]

theorem circFree_nAnd {M N : Neg} (hM : CircFreeN M) (hN : CircFreeN N) :
    CircFreeN (nAnd M N) := ⟨hM, hN⟩

theorem circFree_nOr {M N : Neg} (hM : CircFreeN M) (hN : CircFreeN N) :
    CircFreeN (nOr M N) := ⟨hM, hN⟩

theorem circFree_nAndAll {l : List Neg} (h : ∀ x ∈ l, CircFreeN x) :
    CircFreeN (nAndAll l) := by
  induction l with
  | nil => exact circFree_nTop
  | cons x l ih =>
      exact circFree_nAnd (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem circFree_nOrAll {l : List Neg} (h : ∀ x ∈ l, CircFreeN x) :
    CircFreeN (nOrAll l) := by
  induction l with
  | nil => exact circFree_nBot
  | cons x l ih =>
      exact circFree_nOr (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem circFree_pGuard {p a : String} {C D : Neg}
    (hC : CircFreeN C) (hD : CircFreeN D) : CircFreeN (pGuard p a C D) := by
  unfold pGuard; split
  · exact hC
  · exact hD

theorem circFree_atomHead {p q : String} : ∀ x ∈ atomHead p q, CircFreeN x := by
  unfold atomHead; split
  · intro x hx; exact absurd hx List.not_mem_nil
  · intro x hx
    rcases List.mem_singleton.mp hx with rfl
    exact trivial

/-- A split of a ◯-free context has a ◯-free head and a ◯-free residue. -/
theorem circFree_splits {Γ : List Neg} (h : CircFreeCtx Γ) :
    ∀ {X rest}, (X, rest) ∈ splits Γ → CircFreeN X ∧ CircFreeCtx rest := by
  induction Γ with
  | nil => intro X rest hm; simp [splits] at hm
  | cons Y Γ ih =>
      intro X rest hm
      simp only [splits, List.mem_cons, List.mem_map] at hm
      have hY : CircFreeN Y := h Y (List.mem_cons_self ..)
      have hΓ : CircFreeCtx Γ := fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)
      rcases hm with hm | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases hm; exact ⟨hY, hΓ⟩
      · cases hEq
        refine ⟨(ih hΓ hZ).1, fun W hW => ?_⟩
        rcases List.mem_cons.mp hW with rfl | hW
        · exact hY
        · exact (ih hΓ hZ).2 W hW

/-- Inverting a ◯-free positive gives ◯-free branches. -/
theorem circFree_invertPos : ∀ (P : Pos), CircFreeP P →
    ∀ b ∈ invertPos P, CircFreeCtx b
  | .atom _, _, b, hb => by
      rw [invertPos_atom] at hb
      rcases List.mem_singleton.mp hb with rfl
      intro Z hZ
      rcases List.mem_singleton.mp hZ with rfl
      exact trivial
  | .fls, _, b, hb => by
      rw [invertPos_fls] at hb; exact absurd hb List.not_mem_nil
  | .or P Q, h, b, hb => by
      rw [invertPos_or] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact circFree_invertPos P h.1 b hb
      · exact circFree_invertPos Q h.2 b hb
  | .down M, h, b, hb => by
      rw [invertPos_down] at hb
      rcases List.mem_singleton.mp hb with rfl
      intro Z hZ
      rcases List.mem_singleton.mp hZ with rfl
      exact h
termination_by P => sizePos P
decreasing_by all_goals (simp only [sizePos]; omega)

/-- The fire scan returns a ◯-free continuation and residue. -/
theorem circFree_findFire {Γ : List Neg} (h : CircFreeCtx Γ) {a : String}
    {N : Neg} {rest : List Neg} (hf : findFire Γ (splits Γ) = some (a, N, rest)) :
    CircFreeN N ∧ CircFreeCtx rest := by
  have hm := findFire_mem hf
  obtain ⟨hX, hr⟩ := circFree_splits h hm
  exact ⟨hX.2, hr⟩

theorem circFree_head {X : Neg} {Γ : List Neg} (h : CircFreeCtx (X :: Γ)) :
    CircFreeN X := h X (List.mem_cons_self ..)

theorem circFree_tail {X : Neg} {Γ : List Neg} (h : CircFreeCtx (X :: Γ)) :
    CircFreeCtx Γ := fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)

theorem circFree_cons {X : Neg} {Γ : List Neg} (hX : CircFreeN X)
    (h : CircFreeCtx Γ) : CircFreeCtx (X :: Γ) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hX
  · exact h Z hZ

theorem circFree_nil : CircFreeCtx ([] : List Neg) :=
  fun _ h => absurd h List.not_mem_nil

theorem circFree_append {Γ Δ : List Neg} (hΓ : CircFreeCtx Γ) (hΔ : CircFreeCtx Δ) :
    CircFreeCtx (Γ ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact hΓ Z hZ
  · exact hΔ Z hZ

set_option maxHeartbeats 4000000 in
/-- **`interpP` preserves ◯-freeness.**  The obligation `CircFreeInterpP`,
discharged.  Structure as `interpP_pfree`: a three-way `first` clears the
fuel-0 defaults, the inert hypotheses and everything unreachable; the aggregate
clauses are taken by `fun_induction`'s own case numbering.  Unreachable here,
and not there: the two ◯-carrying processing clauses (a `◯Q` or a `↓◯Q′ ⊃ N`
in `todo` contradicts `CircFreeCtx todo`), the seven ◯-goal aggregates
(`OptCircFree (some (◯Q))` is `False`), and the `circ` arm of every station-row
match (`CircFreeCtx done` and `splits`). -/
theorem interpP_circFreeN (p : String) :
    ∀ (f : Nat) (todo done : List Neg) (g : Option Neg),
      CircFreeCtx todo → CircFreeCtx done → OptCircFree g →
      CircFreeN (interpP p f todo done g) := by
  intro f todo done g
  fun_induction interpP p f todo done g
  all_goals intro ht hd hg
  all_goals try (first
    | exact circFree_nTop
    | exact circFree_nBot
    | exact (circFree_head ht).elim
    | exact (circFree_head ht).1.elim
    | exact hg.elim)
  -- the PARKING clauses: the head moves from `todo` to `done` unchanged
  case case3 | case11 | case12 | case13 | case14 | case15 =>
    rename_i ih
    exact ih (circFree_tail ht) (circFree_cons (circFree_head ht) hd) hg
  -- `↑(P∨Q)` in `todo`, `∃p` mode: the disjunction of the branch results
  case case6 =>
    rename_i ihB
    apply circFree_nOrAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    exact ihB b (circFree_append (circFree_invertPos _ (circFree_head ht) b hb)
      (circFree_tail ht)) hd hg
  -- `↑(P∨Q)` in `todo`, `∀p` mode: each branch conjunct guarded by its `∃p`
  case case7 =>
    rename_i ihE ihA
    apply circFree_nAndAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    have hbc : CircFreeCtx (b ++ _) :=
      circFree_append (circFree_invertPos _ (circFree_head ht) b hb) (circFree_tail ht)
    exact ⟨ihE b hbc hd trivial, ihA b hbc hd hg⟩
  -- `↑↓M` in `todo`: the negative moves in
  case case8 =>
    rename_i ih
    have hM := circFree_head ht
    simp only [CircFreeN, CircFreeP] at hM
    exact ih (circFree_cons hM (circFree_tail ht)) hd hg
  -- `M ∧ N` in `todo`: the conjunction splits
  case case9 =>
    rename_i ih
    exact ih (circFree_cons (circFree_head ht).1
      (circFree_cons (circFree_head ht).2 (circFree_tail ht))) hd hg
  -- `⊥ ⊃ N` is inert
  case case10 =>
    rename_i ih
    exact ih (circFree_tail ht) hd hg
  -- the fire step: the continuation and the residue come out of `splits`
  case case18 =>
    rename_i hfire ih
    obtain ⟨hN, hrest⟩ := circFree_findFire hd hfire
    exact ih (circFree_cons hN circFree_nil) hrest hg
  -- the `∃p` aggregate at a saturated station
  case case19 =>
    rename_i ihFire ihDykG ihDykRes ihBox ihCimpG ihRes ihOrG ihStripG ihAndG
    apply circFree_nAndAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
    obtain ⟨hX, hrest⟩ := circFree_splits hd hXr
    cases X with
    | up P => cases P <;> first | exact circFree_pGuard circFree_nTop trivial
                                | exact circFree_nTop
    | imp Q N =>
        cases Q with
        | atom a =>
            exact circFree_pGuard circFree_nTop
              ⟨trivial, ihFire rest N (circFree_cons hX.2 circFree_nil) hrest trivial⟩
        | fls => exact circFree_nTop
        | or Qa Qb =>
            exact ⟨⟨ihOrG Qa Qb circFree_nil hd hX.1,
                    ihFire rest N (circFree_cons hX.2 circFree_nil) hrest trivial⟩,
                   ihRes rest circFree_nil hrest trivial⟩
        | down M =>
            cases M with
            | up Pa =>
                exact ⟨⟨ihStripG Pa circFree_nil hd hX.1,
                        ihFire rest N (circFree_cons hX.2 circFree_nil) hrest trivial⟩,
                       ihRes rest circFree_nil hrest trivial⟩
            | and Ma Mb =>
                exact ⟨⟨ihAndG Ma Mb circFree_nil hd hX.1,
                        ihFire rest N (circFree_cons hX.2 circFree_nil) hrest trivial⟩,
                       ihRes rest circFree_nil hrest trivial⟩
            | imp Q' N' =>
                exact ⟨⟨ihDykG Q' N' circFree_nil hd hX.1,
                        ihFire rest N (circFree_cons hX.2 circFree_nil) hrest trivial⟩,
                       ihDykRes rest N' N
                         (circFree_cons ⟨hX.1.2, hX.2⟩ circFree_nil) hrest trivial⟩
            | circ Q' => exact hX.1.elim
    | and _ _ => exact circFree_nTop
    | circ Q => exact hX.elim
  -- `∀p` at an implication goal: each branch conjunct guarded by its `∃p`
  case case20 =>
    rename_i ihE ihA
    apply circFree_nAndAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    have hbc : CircFreeCtx b := circFree_invertPos _ hg.1 b hb
    exact ⟨ihE b hbc hd trivial, ihA b hbc hd hg.2⟩
  -- `∀p` at a conjunctive goal
  case case21 =>
    rename_i ihM ihN
    exact ⟨ihM circFree_nil hd hg.1, ihN circFree_nil hd hg.2⟩
  -- `∀p` at `↑q` with `q` absent: the atom head and the station rows
  case case23 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply circFree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact circFree_atomHead x hx
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      obtain ⟨hX, hrest⟩ := circFree_splits hd hXr
      cases X with
      | up P => cases P <;> exact circFree_nBot
      | imp Q N =>
          cases Q with
          | atom a =>
              exact circFree_pGuard circFree_nBot
                ⟨trivial, ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
          | fls => exact circFree_nBot
          | or Qa Qb =>
              exact ⟨ihOr Qa Qb circFree_nil hd hX.1,
                     ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
          | down M =>
              cases M with
              | up Pa =>
                  exact ⟨ihStrip Pa circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | and Ma Mb =>
                  exact ⟨ihAnd Ma Mb circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | imp Q' N' =>
                  exact ⟨ihDyk Q' N' circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | circ Q' => exact hX.1.elim
      | and _ _ => exact circFree_nBot
      | circ Q => exact hX.elim
  -- `∀p` at `↑⊥`: the rows alone
  case case24 =>
    rename_i ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply circFree_nOrAll
    intro x hx
    simp only [List.mem_map, List.mem_attach, true_and] at hx
    obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
    obtain ⟨hX, hrest⟩ := circFree_splits hd hXr
    cases X with
    | up P => cases P <;> exact circFree_nBot
    | imp Q N =>
        cases Q with
        | atom a =>
            exact circFree_pGuard circFree_nBot
              ⟨trivial, ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
        | fls => exact circFree_nBot
        | or Qa Qb =>
            exact ⟨ihOr Qa Qb circFree_nil hd hX.1,
                   ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
        | down M =>
            cases M with
            | up Pa =>
                exact ⟨ihStrip Pa circFree_nil hd hX.1,
                       ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
            | and Ma Mb =>
                exact ⟨ihAnd Ma Mb circFree_nil hd hX.1,
                       ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
            | imp Q' N' =>
                exact ⟨ihDyk Q' N' circFree_nil hd hX.1,
                       ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
            | circ Q' => exact hX.1.elim
    | and _ _ => exact circFree_nBot
    | circ Q => exact hX.elim
  -- `∀p` at `↑(P₁∨P₂)`: the two goal-inversion heads and the rows
  case case25 =>
    rename_i ihP1 ihP2 ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply circFree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ihP1 circFree_nil hd hg.1
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ihP2 circFree_nil hd hg.2
        · exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      obtain ⟨hX, hrest⟩ := circFree_splits hd hXr
      cases X with
      | up P => cases P <;> exact circFree_nBot
      | imp Q N =>
          cases Q with
          | atom a =>
              exact circFree_pGuard circFree_nBot
                ⟨trivial, ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
          | fls => exact circFree_nBot
          | or Qa Qb =>
              exact ⟨ihOr Qa Qb circFree_nil hd hX.1,
                     ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
          | down M =>
              cases M with
              | up Pa =>
                  exact ⟨ihStrip Pa circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | and Ma Mb =>
                  exact ⟨ihAnd Ma Mb circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | imp Q' N' =>
                  exact ⟨ihDyk Q' N' circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | circ Q' => exact hX.1.elim
      | and _ _ => exact circFree_nBot
      | circ Q => exact hX.elim
  -- `∀p` at `↑↓M`: the goal-inversion head and the rows
  case case26 =>
    rename_i ihM ihFire ihDyk ihCimp ihOr ihStrip ihAnd
    apply circFree_nOrAll
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ihM circFree_nil hd hg
      · exact absurd hx List.not_mem_nil
    · simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      obtain ⟨hX, hrest⟩ := circFree_splits hd hXr
      cases X with
      | up P => cases P <;> exact circFree_nBot
      | imp Q N =>
          cases Q with
          | atom a =>
              exact circFree_pGuard circFree_nBot
                ⟨trivial, ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
          | fls => exact circFree_nBot
          | or Qa Qb =>
              exact ⟨ihOr Qa Qb circFree_nil hd hX.1,
                     ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
          | down M' =>
              cases M' with
              | up Pa =>
                  exact ⟨ihStrip Pa circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | and Ma Mb =>
                  exact ⟨ihAnd Ma Mb circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | imp Q' N' =>
                  exact ⟨ihDyk Q' N' circFree_nil hd hX.1,
                         ihFire rest N (circFree_cons hX.2 circFree_nil) hrest hg⟩
              | circ Q' => exact hX.1.elim
      | and _ _ => exact circFree_nBot
      | circ Q => exact hX.elim

/-- The obligation, DISCHARGED. -/
theorem circFreeInterpP (p : String) : CircFreeInterpP p :=
  fun f done g hd hg => interpP_circFreeN p f [] done g circFree_nil hd hg

end CircFreeInterp

/-- **N4 ON ◯-FREE STATIONS**, in the interderivable form — the only form that
survives `wip/ui_routeB_n4_lit.lean`.  PROVED relative to `CircFreeInterpP`, which
`circFreeInterpP` discharges:

    n4_circFree : CircFreeInterpP p → SatE2P p → SatA2P p →
                  Saturated done → ParkedCtxP done →
                  CircFreeCtx done → CircFreeN G →
                  EStabilises p done × AStabilises p done G
-/
noncomputable def n4_circFree {p : String} {done : List Neg} {G : Neg}
    (cf : CircFreeInterpP p) (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (hd : CircFreeCtx done) (hG : CircFreeN G) :
    EStabilises p done × AStabilises p done G :=
  stabilises_of_hasUICF cf s2 a2 hsat hP hd hG (hasUICF_circFree hd hG)

/-- **N4 ON ◯-FREE STATIONS, UNCONDITIONAL** over the two cofinality variables.
Both chains of `interpP` are eventually constant up to interderivability at
every saturated parked ◯-free station with a ◯-free goal:

    SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
    CircFreeCtx done → CircFreeN G →
    EStabilises p done × AStabilises p done G

`SatE2P`/`SatA2P` are proved unconditional in `LJF/OFuelPCofinal.lean`
(`LJFO.satE2P`, `LJFO.satA2P`, §4.17); instantiating them here is a one-line
job that belongs with that module.  With them, N4's ◯-free instance is closed,
and `hasUI_of_stabilises` turns it back into `HasUI` for the cell. -/
noncomputable def n4_circFree_uncond {p : String} {done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (hd : CircFreeCtx done) (hG : CircFreeN G) :
    EStabilises p done × AStabilises p done G :=
  n4_circFree (circFreeInterpP p) s2 a2 hsat hP hd hG

end LJFO

/-! ## Pins -/

#axioms_within LJFO.hasUI_of_stabilises [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.isIPL_eraseNeg [propext]
#axioms_within LJFO.pfree_eraseNeg []
#axioms_within LJFO.pfreeN_negOfO []
#axioms_within LJFO.uiE [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.uiA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hasUICF_circFree [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.circFree_splits [propext, Quot.sound]
#axioms_within LJFO.circFree_invertPos [propext, Quot.sound]
#axioms_within LJFO.circFree_findFire [propext, Quot.sound]
#axioms_within LJFO.interpP_circFreeN [propext, Quot.sound]
#axioms_within LJFO.circFreeInterpP [propext, Quot.sound]
#axioms_within LJFO.stabilises_of_hasUICF [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.n4_circFree [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.n4_circFree_uncond [propext, Classical.choice, Quot.sound]
