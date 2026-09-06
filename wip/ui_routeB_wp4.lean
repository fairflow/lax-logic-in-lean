/-
Route (B), work package **WP4**: the transfer of a uniform-interpolant pair
from the SATURATION of a polarised station back to the station itself,
through the PROCESSING phase — and, with it, the inhabitation of
`CellsFor p` (`wip/ui_routeB_n3.lean`, N6) on ◯-free cells.

The shape of the package.  `IsUIPair p Γ G E A` (N2) is a statement about a
STATION `Γ`; `interpP` computes over a GENERALISED station, a pair
`(todo, done)` with `todo` the unprocessed hypotheses and `done` the parked
ones, and every input WP4 needs is already stated at that generality:

* soundness `eSoundP p f todo done : Inv (todo ++ done) [] .tru E_f`
  and `aSoundP p f todo done G : Inv (A_f :: (todo ++ done)) [] .tru G`
  (`LJF/OFuelPSound.lean`), at EVERY `(todo, done)`;
* cofinality through the processing phase `eMinPP`/`aMinPP`
  (`LJF/OFuelPMin.lean`), which take `SatE2P`/`SatA2P` at the saturated
  stations and deliver the same statement at EVERY `(todo, done)`;
* ◯-freeness `interpP_circFreeN` (`wip/ui_routeB_n4.lean`), likewise.

So the whole of WP4 is: state stabilisation at a generalised station
(`EStabilisesP`/`AStabilisesP`, §1) and re-run N3 in both directions over it
(§2, §3).  `EStabilisesP p [] done` is `EStabilises p done` by `rfl`, so
nothing is re-stated and nothing is lost.

**Stage 1 (§4, rule 8) — the ◯-free instance, a THEOREM.**  `[negOfO φ]` for
an IPL formula `φ` is a ◯-free generalised station `(todo, done) =
([negOfO φ], [])`, so `hasUICF_circFree` gives a ◯-restricted pair at
`[negOfO φ] ++ [] = [negOfO φ]` outright (Pitts's theorem, transported), §3
turns it into stabilisation of the two chains at that generalised station,
and §2 turns THAT back into an UNRESTRICTED pair — the ◯-restriction is on
the input only, because `eMinPP`/`aMinPP` are cofinal for ◯-carrying test
data.  Both cells of `CellsFor` arise this way, the second at
`(todo, done) = ([], [])`.  Saturation is never assumed: `eMinPP`/`aMinPP`
run the fire scan themselves.

**Stage 2 (§6) — WP4 in general.**  The same assembly with the stabilisation
at the saturated parked stations reached by processing taken as a PARAMETER
`StabilisationAllP` (the blueprint's N4, restated over `interpP`); the
transfer through the processing phase is the recursion `stabP`, which mirrors
`eMinPP`'s clause list: ten clauses in which `interpP` is LITERALLY the same
formula one fuel down at the successor station, one constant clause, one
branching clause, and the saturated leaf where the parameter is read.

Nothing here is a `sorry`.  `SatE2P`/`SatA2P` are variables throughout, as in
every work package since WP2; `LJFO.satE2P`/`satA2P` (`LJF/OFuelPCofinal.lean`)
instantiate them in one line, deferred with that module.
-/
import wip.ui_routeB_n4
import Meta.Audit

set_option autoImplicit false

namespace LJFO

open PLLND

/-! # 1 · Stabilisation at a GENERALISED station

`EStabilises`/`AStabilises` (`wip/ui_routeB_n3.lean`) fix `todo := []`.  The
same statements at an arbitrary `(todo, done)`; the `[]` instances are the old
ones definitionally (`estabilisesP_nil`, `astabilisesP_nil`, both `rfl`). -/

/-- The `∃p`-chain at the generalised station `(todo, done)` is eventually
constant up to interderivability. -/
def EStabilisesP (p : String) (todo done : List Neg) : Type :=
  Σ f₀ : Nat, ∀ f, f₀ ≤ f →
    Inv [interpP p f₀ todo done none] [] .tru (interpP p f todo done none) ×
    Inv [interpP p f todo done none] [] .tru (interpP p f₀ todo done none)

/-- The `∀p`-chain at the generalised station `(todo, done)` is eventually
constant modulo the `∃p`-chain. -/
def AStabilisesP (p : String) (todo done : List Neg) (G : Neg) : Type :=
  Σ f₀ : Nat, ∀ f, f₀ ≤ f →
    Inv [interpP p f todo done none, interpP p f₀ todo done (some G)] [] .tru
      (interpP p f todo done (some G)) ×
    Inv [interpP p f todo done none, interpP p f todo done (some G)] [] .tru
      (interpP p f₀ todo done (some G))

/-- At an empty `todo` the generalised statement IS N1's. -/
theorem estabilisesP_nil {p : String} {done : List Neg} :
    EStabilisesP p [] done = EStabilises p done := rfl

/-- Likewise on the `∀p` side. -/
theorem astabilisesP_nil {p : String} {done : List Neg} {G : Neg} :
    AStabilisesP p [] done G = AStabilises p done G := rfl

/-! # 2 · N3 forward through the processing phase

`hasUI_of_stabilises` (`wip/ui_routeB_n4.lean`) verbatim, with the two
cofinality variables replaced by their processing-phase closures `eMinPP
s2 todo done` / `aMinPP a2 todo done` and the soundness lemmas read at
`(todo, done)`.  The saturation hypothesis DISAPPEARS: `eMinPP`/`aMinPP`
run the fire scan and reach the saturated station themselves, and it is
there — inside them — that `SatE2P`/`SatA2P` are consumed.

`cutInv` enters exactly where it does in `hasUI_of_stabilises`: once in
`minE`, three times in `minA`. -/

/-- **N3, forward, at a generalised station.**  If both chains of
`(todo, done)` are eventually constant up to interderivability, their values
at the thresholds are a uniform-interpolant pair for the cell
`todo ++ done ⇒ G`, against UNRESTRICTED `p`-free test data:

    SatE2P p → SatA2P p → ParkedCtxP done →
    EStabilisesP p todo done → AStabilisesP p todo done G →
    HasUI p (todo ++ done) G
-/
noncomputable def isUIPair_of_stabilisesP {p : String} {todo done : List Neg}
    {G : Neg} (s2 : SatE2P p) (a2 : SatA2P p) (hP : ParkedCtxP done)
    (f₀ f₁ : Nat)
    (hE : ∀ f, f₀ ≤ f →
      Inv [interpP p f₀ todo done none] [] .tru (interpP p f todo done none) ×
      Inv [interpP p f todo done none] [] .tru (interpP p f₀ todo done none))
    (hA : ∀ f, f₁ ≤ f →
      Inv [interpP p f todo done none, interpP p f₁ todo done (some G)] [] .tru
        (interpP p f todo done (some G)) ×
      Inv [interpP p f todo done none, interpP p f todo done (some G)] [] .tru
        (interpP p f₁ todo done (some G))) :
    IsUIPair p (todo ++ done) G
      (interpP p f₀ todo done none) (interpP p f₁ todo done (some G)) := by
  refine
    { pfreeE := interpP_pfree p _ _ _ _
      pfreeA := interpP_pfree p _ _ _ _
      soundE := eSoundP p f₀ todo done
      soundA := aSoundP p f₁ todo done G
      minE := ?_
      minA := ?_ }
  · -- `E_{f₀} ⊢ E_k` (stabilisation) composed with `E_k, Δ ⊢ⱼ ψ` (cofinality)
    intro Δ ψ hΔ hψ j d
    obtain ⟨n, hw⟩ := eMinPP s2 todo done Δ ψ hP hΔ hψ d
    have hd : Inv (interpP p (n + f₀) todo done none :: Δ) [] j ψ :=
      hw (n + f₀) (Nat.le_add_right _ _)
    have hstab : Inv [interpP p f₀ todo done none] [] .tru
        (interpP p (n + f₀) todo done none) :=
      (hE (n + f₀) (Nat.le_add_left _ _)).1
    exact cutInv _ _ _ _ _ hstab hd
  · -- `E_{f₀} ⊢ E_k`, `E_k, Δ ⊢ A_k` (cofinality), `E_k, A_k ⊢ A_{f₁}`
    intro Δ hΔ d
    obtain ⟨m, hw⟩ := aMinPP a2 todo done Δ G hP hΔ d
    have hk : Inv (interpP p (m + f₀ + f₁) todo done none :: Δ) [] .tru
        (interpP p (m + f₀ + f₁) todo done (some (jGoal .tru G))) :=
      hw (m + f₀ + f₁) (m + f₀ + f₁) (by omega) (by omega)
    rw [jGoal_tru] at hk
    have hEk : Inv [interpP p f₀ todo done none] [] .tru
        (interpP p (m + f₀ + f₁) todo done none) := (hE (m + f₀ + f₁) (by omega)).1
    -- (1) `E_{f₀}, Δ ⊢ A_k`
    have d1 : Inv (interpP p f₀ todo done none :: Δ) [] .tru
        (interpP p (m + f₀ + f₁) todo done (some G)) :=
      cutInv _ _ _ _ _ hEk hk
    -- (2) `A_k, E_k ⊢ A_{f₁}`, from the ∀p stabilisation, permuted
    have d2 : Inv (interpP p (m + f₀ + f₁) todo done (some G) ::
        [interpP p (m + f₀ + f₁) todo done none]) [] .tru
        (interpP p f₁ todo done (some G)) :=
      (hA (m + f₀ + f₁) (by omega)).2.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact absurd hZ List.not_mem_nil)
    -- (3) cut `A_k`
    have d3 : Inv ((interpP p f₀ todo done none :: Δ) ++
        [interpP p (m + f₀ + f₁) todo done none]) [] .tru
        (interpP p f₁ todo done (some G)) := cutInv _ _ _ _ _ d1 d2
    -- (4) cut `E_k` away against the ∃p stabilisation, then contract
    have d4 : Inv (interpP p (m + f₀ + f₁) todo done none ::
        (interpP p f₀ todo done none :: Δ)) [] .tru
        (interpP p f₁ todo done (some G)) :=
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

/-- **N3, forward, at a generalised station**, with the interpolants existentially
packed:

    SatE2P p → SatA2P p → ParkedCtxP done →
    EStabilisesP p todo done → AStabilisesP p todo done G →
    HasUI p (todo ++ done) G
-/
noncomputable def hasUI_of_stabilisesP {p : String} {todo done : List Neg}
    {G : Neg} (s2 : SatE2P p) (a2 : SatA2P p) (hP : ParkedCtxP done)
    (he : EStabilisesP p todo done) (ha : AStabilisesP p todo done G) :
    HasUI p (todo ++ done) G :=
  ⟨_, _, isUIPair_of_stabilisesP s2 a2 hP he.1 ha.1 he.2 ha.2⟩

/-! # 3 · N3 backward through the processing phase, ◯-restricted

`stabilises_of_hasUICF` verbatim, at a generalised station.  The pair's
minimality is tested at exactly two places, both built from `interpP` at
`(todo, done)` itself, and `interpP_circFreeN` certifies both ◯-free — which
is why a ◯-RESTRICTED pair is enough to make the chains stabilise. -/

/-- **N3, backward, at a generalised station**, for the ◯-restricted pair:

    SatE2P p → SatA2P p → ParkedCtxP done →
    CircFreeCtx todo → CircFreeCtx done → CircFreeN G →
    HasUICF p (todo ++ done) G →
    EStabilisesP p todo done × AStabilisesP p todo done G
-/
noncomputable def stabilises_of_hasUICFP {p : String} {todo done : List Neg}
    {G : Neg} (s2 : SatE2P p) (a2 : SatA2P p) (hP : ParkedCtxP done)
    (ht : CircFreeCtx todo) (hd : CircFreeCtx done) (hG : CircFreeN G)
    (h : HasUICF p (todo ++ done) G) :
    EStabilisesP p todo done × AStabilisesP p todo done G := by
  obtain ⟨E, A, u⟩ := h
  have hEdone : Inv ((todo ++ done) ++ []) [] .tru E :=
    u.soundE.wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ))
  obtain ⟨n, hv⟩ := eMinPP s2 todo done [] E hP pfreeCtx_nil u.pfreeE hEdone
  have hAdone : Inv ((todo ++ done) ++ [A]) [] .tru G :=
    u.soundA.wk (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      · exact List.mem_append.mpr (Or.inl hZ))
  obtain ⟨m, hw⟩ :=
    aMinPP a2 todo done [A] G hP (pfreeCtx_singleton u.pfreeA) hAdone
  -- `E ⊢ E_k`: the ∃p approximant at a ◯-free generalised station is ◯-free
  have hEmin : ∀ k : Nat, Inv (E :: []) [] .tru (interpP p k todo done none) :=
    fun k => u.minE [] _ pfreeCtx_nil (interpP_pfree p _ _ _ _)
      (fun _ hZ => absurd hZ List.not_mem_nil)
      (interpP_circFreeN p k todo done none ht hd trivial)
      ((eSoundP p k todo done).wk (fun Z hZ => List.mem_append.mpr (Or.inl hZ)))
  -- `E, A_k ⊢ A`: likewise for the ∀p approximant
  have hAmin : ∀ k : Nat,
      Inv (E :: [interpP p k todo done (some G)]) [] .tru A :=
    fun k => u.minA _ (pfreeCtx_singleton (interpP_pfree p _ _ _ _))
      (fun Z hZ => by
        rcases List.mem_singleton.mp hZ with rfl
        exact interpP_circFreeN p k todo done (some G) ht hd hG)
      ((aSoundP p k todo done G).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
        · exact List.mem_append.mpr (Or.inl hZ)))
  refine ⟨⟨n + m, fun f hf => ⟨?_, ?_⟩⟩, ⟨n + m, fun f hf => ⟨?_, ?_⟩⟩⟩
  · exact cutInv _ _ _ _ _ (hv (n + m) (by omega)) (hEmin f)
  · exact cutInv _ _ _ _ _ (hv f (by omega)) (hEmin (n + m))
  · have hEf : Inv (interpP p f todo done none :: []) [] .tru E := hv f (by omega)
    have hA : Inv ([interpP p f todo done none] ++
        [interpP p (n + m) todo done (some G)]) [] .tru A :=
      cutInv _ _ _ _ _ hEf (hAmin (n + m))
    have hcof : Inv (interpP p f todo done none :: [A]) [] .tru
        (interpP p f todo done (some (jGoal .tru G))) := hw f f (by omega) (by omega)
    rw [jGoal_tru] at hcof
    have hcof' : Inv (A :: [interpP p f todo done none]) [] .tru
        (interpP p f todo done (some G)) :=
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
  · have hEf : Inv (interpP p f todo done none :: []) [] .tru E := hv f (by omega)
    have hA : Inv ([interpP p f todo done none] ++
        [interpP p f todo done (some G)]) [] .tru A :=
      cutInv _ _ _ _ _ hEf (hAmin f)
    have hcof : Inv (interpP p f todo done none :: [A]) [] .tru
        (interpP p (n + m) todo done (some (jGoal .tru G))) :=
      hw f (n + m) (by omega) (by omega)
    rw [jGoal_tru] at hcof
    have hcof' : Inv (A :: [interpP p f todo done none]) [] .tru
        (interpP p (n + m) todo done (some G)) :=
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

/-! # 4 · Stage 1 · the ◯-free instance of `CellsFor` (rule 8)

`isIPL φ` makes `negOfO φ` ◯-free, so `hasUICF_circFree` — Pitts's theorem
transported through the polarisation — supplies a ◯-restricted pair at the
cell, §3 turns it into stabilisation at the GENERALISED station, and §2 turns
that into an UNRESTRICTED pair.  The ◯-restriction does not propagate: it is
consumed by §3 and never reappears, because `eMinPP`/`aMinPP` are cofinal for
◯-CARRYING `p`-free test data at a ◯-free station. -/

mutual
/-- Polarising an IPL formula positively gives a ◯-free positive. -/
theorem circFree_posOfO : ∀ {φ : PLLFormula}, isIPL φ → CircFreeP (posOfO φ)
  | .prop _, _ => trivial
  | .falsePLL, _ => trivial
  | .or _ _, h => ⟨circFree_posOfO h.1, circFree_posOfO h.2⟩
  | .and _ _, h => ⟨circFree_negOfO h.1, circFree_negOfO h.2⟩
  | .ifThen _ _, h => ⟨circFree_posOfO h.1, circFree_negOfO h.2⟩
  | .somehow _, h => h.elim
/-- Polarising an IPL formula negatively gives a ◯-free negative. -/
theorem circFree_negOfO : ∀ {φ : PLLFormula}, isIPL φ → CircFreeN (negOfO φ)
  | .prop _, _ => trivial
  | .falsePLL, _ => trivial
  | .or _ _, h => ⟨circFree_posOfO h.1, circFree_posOfO h.2⟩
  | .and _ _, h => ⟨circFree_negOfO h.1, circFree_negOfO h.2⟩
  | .ifThen _ _, h => ⟨circFree_posOfO h.1, circFree_negOfO h.2⟩
  | .somehow _, h => h.elim
end

/-- **N4 at a ◯-free GENERALISED station, unconditional** over the two
cofinality variables.  `hasUICF_circFree` needs neither saturation nor
parking, so the only hypotheses are ◯-freeness and the parked-shape invariant
that `eMinPP`/`aMinPP` require of `done`. -/
noncomputable def n4P_circFree {p : String} {todo done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p) (hP : ParkedCtxP done)
    (ht : CircFreeCtx todo) (hd : CircFreeCtx done) (hG : CircFreeN G) :
    EStabilisesP p todo done × AStabilisesP p todo done G :=
  stabilises_of_hasUICFP s2 a2 hP ht hd hG
    (hasUICF_circFree (circFree_append ht hd) hG)

/-- **A uniform-interpolant pair at a ◯-free generalised station**, against
UNRESTRICTED `p`-free test data. -/
noncomputable def hasUI_circFreeP {p : String} {todo done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p) (hP : ParkedCtxP done)
    (ht : CircFreeCtx todo) (hd : CircFreeCtx done) (hG : CircFreeN G) :
    HasUI p (todo ++ done) G :=
  let w := n4P_circFree s2 a2 hP ht hd hG
  hasUI_of_stabilisesP s2 a2 hP w.1 w.2

/-- **STAGE 1 — `CellsFor` on ◯-free cells, PROVED.**

    cellsFor_circFree : SatE2P p → SatA2P p → ∀ φ, isIPL φ →
                        HasUI p [negOfO φ] (negOfO φ) × HasUI p [] (negOfO φ)

The first cell is the generalised station `([negOfO φ], [])` — the whole
processing phase of `[negOfO φ]` lives inside `eMinPP`/`aMinPP` — and the
second is `([], [])`. -/
noncomputable def cellsFor_circFree {p : String} (s2 : SatE2P p) (a2 : SatA2P p)
    (φ : PLLFormula) (hφ : isIPL φ) :
    HasUI p [negOfO φ] (negOfO φ) × HasUI p [] (negOfO φ) :=
  let hcf : CircFreeN (negOfO φ) := circFree_negOfO hφ
  ⟨hasUI_circFreeP (todo := [negOfO φ]) (done := []) s2 a2 ParkedCtxP.nil
      (circFree_cons hcf circFree_nil) circFree_nil hcf,
   hasUI_circFreeP (todo := []) (done := []) s2 a2 ParkedCtxP.nil
      circFree_nil circFree_nil hcf⟩

/-! # 5 · What N6 gets out of Stage 1: uniform interpolation for PLL on IPC
formulas

`isUIPairPLL_of_isUIPair` erases the pair, so the output is `IsUIPairPLL p φ
E A` — Pitts's pair for `φ` in `LaxND` — with `E`, `A` PLL formulas and the
test formula `ψ` an ARBITRARY `p`-free PLL formula, `◯` included.  Restricted
to `isIPL φ`, that is `PLL_UI`'s statement on IPC formulas. -/

/-- **Uniform interpolation for PLL, restricted to IPC formulas.**  Note what
is NOT restricted: the interpolants `E`, `A` are tested against every `p`-free
PLL formula (`IsUIPairPLL.minE`/`minA`), `◯` included. -/
def IPC_UI_routeB : Type :=
  ∀ (p : String) (φ : PLLFormula), isIPL φ → Σ (E A : PLLFormula), IsUIPairPLL p φ E A

/-- **STAGE 1's consequence for N6.**  Route (B) delivers uniform
interpolation for PLL at every IPC formula. -/
noncomputable def ipc_ui_routeB (s2 : ∀ p, SatE2P p) (a2 : ∀ p, SatA2P p) :
    IPC_UI_routeB := by
  intro p φ hφ
  obtain ⟨⟨E, A₁, uE⟩, ⟨E₀, A, uA⟩⟩ := cellsFor_circFree (s2 p) (a2 p) φ hφ
  exact ⟨eraseNeg E, eraseNeg A, isUIPairPLL_of_isUIPair cutInvOb uE uA⟩

/-! ## 5b · The check against `LJFIPC.uniform_interpolation_IPC`

Route (B)'s interpolants at an IPC formula are values of `interpP` at a ◯-free
generalised station, so they are ◯-free (`interpP_circFreeN`) and their
erasures are IPL formulas (`isIPL_eraseNeg`).  That is exactly what Pitts's
minimality needs of a test formula, so the two constructions can be compared,
and they AGREE up to interderivability in `LaxND`. -/

/-- Stage 1's pair with the interpolants named and certified IPL — the data
the comparison needs and `IsUIPairPLL` alone does not carry. -/
structure IPCPairRouteB (p : String) (φ : PLLFormula) : Type where
  E : PLLFormula
  A : PLLFormula
  pair : IsUIPairPLL p φ E A
  iplE : isIPL E
  iplA : isIPL A

/-- Stage 1, with the interpolants named. -/
noncomputable def ipcPairRouteB {p : String} (s2 : SatE2P p) (a2 : SatA2P p)
    (φ : PLLFormula) (hφ : isIPL φ) : IPCPairRouteB p φ :=
  let hcf : CircFreeN (negOfO φ) := circFree_negOfO hφ
  let ht : CircFreeCtx [negOfO φ] := circFree_cons hcf circFree_nil
  let w1 := n4P_circFree (todo := [negOfO φ]) (done := []) s2 a2
    ParkedCtxP.nil ht circFree_nil hcf
  let w2 := n4P_circFree (todo := ([] : List Neg)) (done := []) s2 a2
    ParkedCtxP.nil circFree_nil circFree_nil hcf
  { E := eraseNeg (interpP p w1.1.1 [negOfO φ] [] none)
    A := eraseNeg (interpP p w2.2.1 [] [] (some (negOfO φ)))
    pair := isUIPairPLL_of_isUIPair cutInvOb
      (isUIPair_of_stabilisesP s2 a2 ParkedCtxP.nil w1.1.1 w1.2.1 w1.1.2 w1.2.2)
      (isUIPair_of_stabilisesP s2 a2 ParkedCtxP.nil w2.1.1 w2.2.1 w2.1.2 w2.2.2)
    iplE := isIPL_eraseNeg
      (interpP_circFreeN p w1.1.1 [negOfO φ] [] none ht circFree_nil trivial)
    iplA := isIPL_eraseNeg
      (interpP_circFreeN p w2.2.1 [] [] (some (negOfO φ))
        circFree_nil circFree_nil hcf) }

/-- **The ◯-free check: route (B) and Pitts's theorem AGREE.**  For an IPC
formula `φ`, route (B)'s `∃p.φ` is interderivable with `LJFIPC.exI p [φ]` and
its `∀p.φ` with `LJFIPC.allI p [] φ`, in `LaxND`.

The two cells are the ones N6 uses: the `∃p` side is the STATION `[φ]`, the
`∀p` side the EMPTY station with goal `φ`.  The `E`-relativisation of Pitts's
`allI_min` is discharged outright, `exI p []` being a theorem. -/
theorem routeB_agrees_IPC {p : String} {φ : PLLFormula} (hφ : isIPL φ)
    (w : IPCPairRouteB p φ) :
    (Nonempty (LaxND [w.E] (LJFIPC.exI p [φ])) ∧
     Nonempty (LaxND [LJFIPC.exI p [φ]] w.E)) ∧
    (Nonempty (LaxND [w.A] (LJFIPC.allI p [] φ)) ∧
     Nonempty (LaxND [LJFIPC.allI p [] φ] w.A)) := by
  -- Pitts at the two cells
  obtain ⟨⟨hEp, hEs, hEm⟩, -⟩ :=
    LJFIPC.uniform_interpolation_IPC p [φ] φ
      (fun _ hψ => by rcases List.mem_singleton.mp hψ with rfl; exact hφ) hφ
  obtain ⟨⟨h0p, h0s, -⟩, ⟨hAp, hAs, hAm⟩⟩ :=
    LJFIPC.uniform_interpolation_IPC p [] φ
      (fun _ hψ => absurd hψ List.not_mem_nil) hφ
  -- `p`-freeness of route (B)'s interpolants, as PLL formulas
  have hEpf : LJFIPC.PFree p w.E := by
    have h := pfree_eraseNeg w.pair.pfreeE
    rwa [(erase_polarise w.E).2] at h
  have hApf : LJFIPC.PFree p w.A := by
    have h := pfree_eraseNeg w.pair.pfreeA
    rwa [(erase_polarise w.A).2] at h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- `E ⊢ ∃p[φ]`: route (B)'s minimality at the `p`-free test formula `∃p[φ]`
    exact w.pair.minE _ (pfreeN_negOfO hEp) hEs
  · -- `∃p[φ] ⊢ E`: Pitts's minimality at the IPL test formula `E`
    exact hEm [] w.E (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => absurd h List.not_mem_nil) w.iplE hEpf w.pair.soundE
  · -- `A ⊢ ∀p φ`: Pitts's minimality, then cut the derivable `∃p[]` away
    obtain ⟨d⟩ := hAm [w.A] (fun _ h => by
        rcases List.mem_singleton.mp h with rfl; exact w.iplA)
      (fun _ h => by rcases List.mem_singleton.mp h with rfl; exact hApf)
      w.pair.soundA
    obtain ⟨e⟩ := h0s
    exact ⟨LaxND.cut1 (e.rename (fun _ h => absurd h List.not_mem_nil)) d⟩
  · -- `∀p φ ⊢ A`: route (B)'s minimality at the `p`-free test formula `∀p φ`
    exact w.pair.minA _ (pfreeN_negOfO hAp) hAs

end LJFO

/-! ## Pins (Stage 1)

Measured with `#axioms_within_pin`, not retyped.  `Classical.choice` is
inherited from `cutInv` (`LJF/OPolInv.lean` §4b) and from
`LJFIPC.uniform_interpolation_IPC`; the two chain statements and the two
polarisation facts are below it. -/

#axioms_within LJFO.EStabilisesP [propext]
#axioms_within LJFO.AStabilisesP [propext]
#axioms_within LJFO.estabilisesP_nil [propext]
#axioms_within LJFO.astabilisesP_nil [propext]
#axioms_within LJFO.circFree_posOfO []
#axioms_within LJFO.circFree_negOfO []
#axioms_within LJFO.isUIPair_of_stabilisesP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hasUI_of_stabilisesP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.stabilises_of_hasUICFP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.n4P_circFree [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hasUI_circFreeP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.cellsFor_circFree [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.IPC_UI_routeB []
#axioms_within LJFO.ipc_ui_routeB [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.IPCPairRouteB []
#axioms_within LJFO.ipcPairRouteB [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.routeB_agrees_IPC [propext, Classical.choice, Quot.sound]
