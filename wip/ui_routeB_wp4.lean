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
`eMinPP`'s clause list: eleven of the thirteen processing clauses (and the
fire step) send `interpP` at `(todo, done)` one fuel up to LITERALLY `interpP`
at the successor station, one clause is constant (`↑⊥`), one branches
(`↑(P ∨ Q)`), and the saturated leaf is where the parameter is read.

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

/-! # 6 · Stage 2 · WP4 in general: the transfer through the processing phase

Stage 1 got its stabilisation from Pitts's theorem, which stops at the ◯-free
fragment.  In general the input is N4 — stabilisation at the SATURATED parked
stations — and WP4 owes the transfer of it back through the processing phase.

The transfer is a recursion on `(todo, done)` with `eMinPP`'s own measure
`2·sum3 todo + sum3 done`, and `interpP`'s clause list makes it short: at
eleven of the thirteen processing clauses, and at the fire step, `interpP` at
`(todo, done)` one fuel up is LITERALLY `interpP` at the successor station,
whatever the goal slot — so stabilisation transfers by rewriting, with no
derivation touched (`StabP.step`).  One clause is constant (`↑⊥`), and ONE
branches (`↑(P ∨ Q)`), where the `∃p` aggregate is an `nOrAll` and the `∀p`
aggregate an `nAndAll` of guarded conjuncts; that clause is the only place a
derivation is built (`stabP_or`), and its one focused step is `andAllImpUse`.

Because the branching clause's `∀p` conjunct guards itself by the branch's own
`∃p` at the SAME fuel, the two chains have to stabilise at a COMMON threshold;
`StabAt`/`StabP` carry one, and `StabAt.raiseTo` moves a witness up to it.
That is where `cutInv` enters the transfer. -/

/-! ## 6.1 Cut in the shapes the transfer uses -/

/-- Cut, one hypothesis: `[M] ⊢ N` and `[N] ⊢ ψ` give `[M] ⊢ ψ`. -/
noncomputable def cut1N {M N ψ : Neg} (d₁ : Inv [M] [] .tru N)
    (d₂ : Inv [N] [] .tru ψ) : Inv [M] [] .tru ψ :=
  cutInv [M] [] .tru N ψ d₁ d₂

/-- Cut at the FIRST of two hypotheses. -/
noncomputable def cut2N {M K N ψ : Neg} (d₁ : Inv [M] [] .tru N)
    (d₂ : Inv [N, K] [] .tru ψ) : Inv [M, K] [] .tru ψ :=
  cutInv [M] [K] .tru N ψ d₁ d₂

/-- Exchange, two hypotheses. -/
def swapInv2 {M K ψ : Neg} (d : Inv [M, K] [] .tru ψ) : Inv [K, M] [] .tru ψ :=
  d.wk (fun Z hZ => by
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact absurd hZ List.not_mem_nil)

/-- Cut at the SECOND of two hypotheses, contracting the first. -/
noncomputable def cut2N' {M K N ψ : Neg} (d₁ : Inv [M, K] [] .tru N)
    (d₂ : Inv [N, M] [] .tru ψ) : Inv [M, K] [] .tru ψ :=
  (cutInv [M, K] [M] .tru N ψ d₁ d₂).wk (fun Z hZ => by
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact hZ
    · rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact absurd hZ List.not_mem_nil)

/-! ## 6.2 The two chains at a COMMON threshold -/

/-- Both chains at a generalised station, stabilising from a GIVEN fuel. -/
def StabAt (p : String) (todo done : List Neg) (G : Neg) (f₀ : Nat) : Type :=
  ∀ f, f₀ ≤ f →
    (Inv [interpP p f₀ todo done none] [] .tru (interpP p f todo done none) ×
     Inv [interpP p f todo done none] [] .tru (interpP p f₀ todo done none)) ×
    (Inv [interpP p f todo done none, interpP p f₀ todo done (some G)] [] .tru
       (interpP p f todo done (some G)) ×
     Inv [interpP p f todo done none, interpP p f todo done (some G)] [] .tru
       (interpP p f₀ todo done (some G)))

/-- Both chains stabilise, at some common threshold. -/
def StabP (p : String) (todo done : List Neg) (G : Neg) : Type :=
  Σ f₀ : Nat, StabAt p todo done G f₀

/-- `UpFrom.mk1` for `StabAt`: `interpP`'s clauses fire at `f+1`, so every
transporter below produces its content in successor form. -/
def StabAt.mk1 {p : String} {todo done : List Neg} {G : Neg} {n : Nat}
    (k : ∀ f', n ≤ f' →
      (Inv [interpP p (n + 1) todo done none] [] .tru
         (interpP p (f' + 1) todo done none) ×
       Inv [interpP p (f' + 1) todo done none] [] .tru
         (interpP p (n + 1) todo done none)) ×
      (Inv [interpP p (f' + 1) todo done none,
            interpP p (n + 1) todo done (some G)] [] .tru
         (interpP p (f' + 1) todo done (some G)) ×
       Inv [interpP p (f' + 1) todo done none,
            interpP p (f' + 1) todo done (some G)] [] .tru
         (interpP p (n + 1) todo done (some G)))) :
    StabAt p todo done G (n + 1)
  | 0, hf => absurd hf (by omega)
  | f' + 1, hf => k f' (by omega)

/-- The `∃p` half. -/
def StabP.toE {p : String} {todo done : List Neg} {G : Neg}
    (w : StabP p todo done G) : EStabilisesP p todo done :=
  ⟨w.1, fun f hf => (w.2 f hf).1⟩

/-- The `∀p` half. -/
def StabP.toA {p : String} {todo done : List Neg} {G : Neg}
    (w : StabP p todo done G) : AStabilisesP p todo done G :=
  ⟨w.1, fun f hf => (w.2 f hf).2⟩

/-- **Raising the threshold**, by cut: `E_n ⊢ E_{f₀} ⊢ E_f` and back, and the
`E`-relativised `∀p` clauses composed the same way. -/
noncomputable def StabAt.raiseTo {p : String} {todo done : List Neg} {G : Neg}
    {f₀ n : Nat} (hn : f₀ ≤ n) (w : StabAt p todo done G f₀) :
    StabAt p todo done G n := by
  intro f hf
  have wn := w n hn
  have wf := w f (Nat.le_trans hn hf)
  have hEfn : Inv [interpP p f todo done none] [] .tru
      (interpP p n todo done none) := cut1N wf.1.2 wn.1.1
  exact ⟨⟨cut1N wn.1.2 wf.1.1, hEfn⟩,
    ⟨cut2N' (cut2N hEfn wn.2.2) (swapInv2 wf.2.1),
     cut2N' wf.2.2 (swapInv2 (cut2N hEfn wn.2.1))⟩⟩

/-- The two SEPARATE stabilisation statements merged at a common threshold —
how the parameter is read at the saturated leaf. -/
noncomputable def stabP_of_stabilises {p : String} {todo done : List Neg}
    {G : Neg} (he : EStabilisesP p todo done) (ha : AStabilisesP p todo done G) :
    StabP p todo done G := by
  refine ⟨he.1 + ha.1, fun f hf => ?_⟩
  have hen := he.2 (he.1 + ha.1) (Nat.le_add_right _ _)
  have hef := he.2 f (by omega)
  have han := ha.2 (he.1 + ha.1) (Nat.le_add_left _ _)
  have haf := ha.2 f (by omega)
  have hEfn : Inv [interpP p f todo done none] [] .tru
      (interpP p (he.1 + ha.1) todo done none) := cut1N hef.2 hen.1
  exact ⟨⟨cut1N hen.2 hef.1, hEfn⟩,
    ⟨cut2N' (cut2N hEfn han.2) (swapInv2 haf.1),
     cut2N' haf.2 (swapInv2 (cut2N hEfn han.1))⟩⟩

/-! ## 6.3 The clause transporters -/

/-- **The single-successor clauses.**  Whenever `interpP` at `(todo, done)`
one fuel up is literally `interpP` at `(todo′, done′)`, whatever the goal
slot, stabilisation transfers by rewriting — no derivation is touched.  Ten of
the twelve processing clauses and the fire step are of this shape. -/
noncomputable def StabP.step {p : String} {todo done todo' done' : List Neg}
    {G : Neg} (w : StabP p todo' done' G)
    (heq : ∀ (f : Nat) (g : Option Neg),
      interpP p (f + 1) todo done g = interpP p f todo' done' g) :
    StabP p todo done G :=
  ⟨w.1 + 1, StabAt.mk1 (fun f' hf' => by
    rw [heq f' none, heq f' (some G), heq w.1 none, heq w.1 (some G)]
    exact w.2 f' hf')⟩

/-- **The absurd hypothesis.**  `↑⊥` in `todo` makes both chains constant from
fuel 1: `⊥` in `∃p` mode, `⊤` in `∀p` mode. -/
noncomputable def stabP_fls {p : String} {todo done : List Neg} {G : Neg} :
    StabP p (.up .fls :: todo) done G := by
  have e1 : ∀ k : Nat, 1 ≤ k →
      interpP p k (.up .fls :: todo) done none = nBot := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [interpP]
  have e2 : ∀ k : Nat, 1 ≤ k →
      interpP p k (.up .fls :: todo) done (some G) = nTop := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [interpP]
  refine ⟨1, fun f hf => ?_⟩
  rw [e1 1 (Nat.le_refl _), e1 f hf, e2 1 (Nat.le_refl _), e2 f hf]
  exact ⟨⟨idNeg _ _ (List.mem_cons_self ..), idNeg _ _ (List.mem_cons_self ..)⟩,
    ⟨nTopIntro, nTopIntro⟩⟩

/-- **Using a `∀p` aggregate hypothesis** — the ONE focused step of the whole
transfer.  From the branch's guard `E` and the aggregate `nAndAll l` carrying
the row `↓E ⊃ A`, the branch's `A` follows:

    [E, nAndAll l] ⊢ A          for  (↓E ⊃ A) ∈ l
-/
noncomputable def andAllImpUse {E A : Neg} {l : List Neg}
    (hmem : Neg.imp (.down E) A ∈ l) : Inv [E, nAndAll l] [] .tru A :=
  simHyp (H := A) (Γ := []) (Δ₀ := [E, nAndAll l])
    (fun hs lf =>
      .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (lfocAndAll hmem
          (.impL (.rfoc (.rel (idNeg E _ (hs _ (List.mem_cons_self ..))))) lf)))
    (fun _ h => absurd h List.not_mem_nil)
    (idNeg A [A] (List.mem_cons_self ..))

/-- **The branching clause.**  `↑(P ∨ Q)` in `todo` sends the `∃p` chain to an
`nOrAll` over the branches and the `∀p` chain to an `nAndAll` of conjuncts
`↓E_branch ⊃ A_branch`; from stabilisation on every branch AT THE COMMON
THRESHOLD, both aggregates stabilise.  The `∃p` side is
`nOrAllElim`/`nOrAllIntro` and spends NO cut; the `∀p` side is `nAndAllIntro`
with `andAllImpUse` and two cuts per row — the branch's guard against the row,
and the row's conclusion against the branch's own `∀p` step. -/
noncomputable def stabP_or_at {p : String} {todo done : List Neg} {G : Neg}
    {P Q : Pos} (n : Nat)
    (brn : ∀ bh : {b : List Neg // b ∈ invertPos (Pos.or P Q)},
      StabAt p (bh.1 ++ todo) done G n) :
    StabAt p (.up (.or P Q) :: todo) done G (n + 1) := by
  have eE : ∀ k : Nat,
      interpP p (k + 1) (.up (.or P Q) :: todo) done none =
        nOrAll ((invertPos (Pos.or P Q)).attach.map
          (fun ⟨b, _⟩ => interpP p k (b ++ todo) done none)) :=
    fun _ => by rw [interpP]
  have eA : ∀ k : Nat,
      interpP p (k + 1) (.up (.or P Q) :: todo) done (some G) =
        nAndAll ((invertPos (Pos.or P Q)).attach.map
          (fun ⟨b, _⟩ =>
            Neg.imp (.down (interpP p k (b ++ todo) done none))
              (interpP p k (b ++ todo) done (some G)))) :=
    fun _ => by rw [interpP]
  refine StabAt.mk1 (fun f' hnf => ?_)
  rw [eE, eE, eA, eA]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- `∃p`: every disjunct of the threshold aggregate implies its own
    refine nOrAllElim _ (List.mem_cons_self ..) ?_
    intro x hx Γ' hsub
    obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
    subst hEq
    exact nOrAllIntro (List.mem_map_of_mem hmem)
      (((brn ⟨b, hb⟩) f' hnf).1.1.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil))
  · refine nOrAllElim _ (List.mem_cons_self ..) ?_
    intro x hx Γ' hsub
    obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
    subst hEq
    exact nOrAllIntro (List.mem_map_of_mem hmem)
      (((brn ⟨b, hb⟩) f' hnf).1.2.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact absurd hZ List.not_mem_nil))
  · -- `∀p`, threshold aggregate ⊢ own aggregate, relative to the `∃p` one
    refine nAndAllIntro ?_
    intro x hx
    obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
    subst hEq
    refine .impR (.downL ?_)
    have hrow : Neg.imp (.down (interpP p n (b ++ todo) done none))
        (interpP p n (b ++ todo) done (some G)) ∈
        (invertPos (Pos.or P Q)).attach.map
          (fun ⟨b, _⟩ =>
            Neg.imp (.down (interpP p n (b ++ todo) done none))
              (interpP p n (b ++ todo) done (some G))) :=
      List.mem_map_of_mem hmem
    refine (cut2N' (cut2N ((brn ⟨b, hb⟩) f' hnf).1.2 (andAllImpUse hrow))
      (swapInv2 ((brn ⟨b, hb⟩) f' hnf).2.1)).wk (fun Z hZ => ?_)
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_self ..
    · rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact absurd hZ List.not_mem_nil
  · refine nAndAllIntro ?_
    intro x hx
    obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
    subst hEq
    refine .impR (.downL ?_)
    have hrow : Neg.imp (.down (interpP p f' (b ++ todo) done none))
        (interpP p f' (b ++ todo) done (some G)) ∈
        (invertPos (Pos.or P Q)).attach.map
          (fun ⟨b, _⟩ =>
            Neg.imp (.down (interpP p f' (b ++ todo) done none))
              (interpP p f' (b ++ todo) done (some G))) :=
      List.mem_map_of_mem hmem
    refine (cut2N' (cut2N ((brn ⟨b, hb⟩) f' hnf).1.1 (andAllImpUse hrow))
      (swapInv2 (cut2N ((brn ⟨b, hb⟩) f' hnf).1.1
        ((brn ⟨b, hb⟩) f' hnf).2.2))).wk (fun Z hZ => ?_)
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_self ..
    · rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      · exact absurd hZ List.not_mem_nil

/-- The branching clause, with the branch thresholds merged. -/
noncomputable def stabP_or {p : String} {todo done : List Neg} {G : Neg}
    {P Q : Pos}
    (br : ∀ bh : {b : List Neg // b ∈ invertPos (Pos.or P Q)},
      StabP p (bh.1 ++ todo) done G) :
    StabP p (.up (.or P Q) :: todo) done G :=
  ⟨maxOver (fun bh => (br bh).1) (invertPos (Pos.or P Q)).attach + 1,
   stabP_or_at _ (fun bh => (br bh).2.raiseTo (le_maxOver (List.mem_attach _ bh)))⟩

/-! ## 6.4 N4 for PLL, as a parameter, and the transfer -/

/-- **N4 for PLL** — OPEN both ways — restated over `interpP`: the two chains
stabilise at every SATURATED parked station.  This is
`wip/ui_routeB_blueprint.lean`'s `StabilisationAll` with `ParkedCtx` replaced
by the parking interpolant's own invariant `ParkedCtxP`. -/
def StabilisationAllP (p : String) : Type :=
  ∀ (done : List Neg) (G : Neg), Saturated done → ParkedCtxP done →
    EStabilises p done × AStabilises p done G

/-- **THE TRANSFER.**  Stabilisation at the saturated parked stations reached
by processing carries back to EVERY generalised station:

    StabilisationAllP p → ∀ todo done G, ParkedCtxP done → StabP p todo done G

The recursion is `eMinPP`'s, on `2·sum3 todo + sum3 done`. -/
noncomputable def stabP {p : String} (par : StabilisationAllP p) :
    ∀ (todo done : List Neg) (G : Neg), ParkedCtxP done → StabP p todo done G
  | .up (.atom a) :: todo, done, G, hP =>
      StabP.step (stabP par todo (.up (.atom a) :: done) G
        (ParkedCtxP.cons (ParkedNP.atom a) hP)) (fun _ _ => by rw [interpP])
  | .up .fls :: _, _, _, _ => stabP_fls
  | .up (.or P Q) :: todo, done, G, hP =>
      stabP_or (fun ⟨b, hb⟩ => stabP par (b ++ todo) done G hP)
  | .up (.down M) :: todo, done, G, hP =>
      StabP.step (stabP par (M :: todo) done G hP) (fun _ _ => by rw [interpP])
  | .and M N :: todo, done, G, hP =>
      StabP.step (stabP par (M :: N :: todo) done G hP) (fun _ _ => by rw [interpP])
  | .imp .fls _ :: todo, done, G, hP =>
      StabP.step (stabP par todo done G hP) (fun _ _ => by rw [interpP])
  | .imp (.atom a) N :: todo, done, G, hP =>
      StabP.step (stabP par todo (.imp (.atom a) N :: done) G
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP)) (fun _ _ => by rw [interpP])
  | .imp (.or Q₁ Q₂) N :: todo, done, G, hP =>
      StabP.step (stabP par todo (.imp (.or Q₁ Q₂) N :: done) G
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP)) (fun _ _ => by rw [interpP])
  | .imp (.down (.up P')) N :: todo, done, G, hP =>
      StabP.step (stabP par todo (.imp (.down (.up P')) N :: done) G
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP)) (fun _ _ => by rw [interpP])
  | .imp (.down (.and M₁ M₂)) N :: todo, done, G, hP =>
      StabP.step (stabP par todo (.imp (.down (.and M₁ M₂)) N :: done) G
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP)) (fun _ _ => by rw [interpP])
  | .imp (.down (.imp Q' N')) N :: todo, done, G, hP =>
      StabP.step (stabP par todo (.imp (.down (.imp Q' N')) N :: done) G
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP)) (fun _ _ => by rw [interpP])
  | .circ Q :: todo, done, G, hP =>
      StabP.step (stabP par todo (.circ Q :: done) G
        (ParkedCtxP.cons (ParkedNP.box Q) hP)) (fun _ _ => by rw [interpP])
  | .imp (.down (.circ Q')) N :: todo, done, G, hP =>
      StabP.step (stabP par todo (.imp (.down (.circ Q')) N :: done) G
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP)) (fun _ _ => by rw [interpP])
  | [], done, G, hP =>
      match hf : findFire done (splits done) with
      | some (_, N', rest) =>
          StabP.step (stabP par [N'] rest G
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP))
            (fun k g => interpPFire_eq (f := k) hf g)
      | none =>
          let w := par done G hf hP
          stabP_of_stabilises w.1 w.2
  termination_by todo done G hP => 2 * sum3 todo + sum3 done
  -- NOT `ljf_dec_e`: this module sees BOTH `LJF/OCore.lean`'s macro and
  -- `LJF/Base.lean`'s (through `LJF.Complete`), and the token is ambiguous.
  -- The alternatives actually needed, spelled out.
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, wNeg, wPos]
    all_goals
      first
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | omega

/-! ## 6.5 What the transfer buys: N5 and N6 -/

/-- **`CellsFor` from N4** — the transfer applied at the two cells N6 needs. -/
noncomputable def cellsFor_of_stab {p : String} (s2 : SatE2P p) (a2 : SatA2P p)
    (par : StabilisationAllP p) : CellsFor p := fun φ =>
  ⟨hasUI_of_stabilisesP (todo := [negOfO φ]) (done := []) s2 a2 ParkedCtxP.nil
      (stabP par [negOfO φ] [] (negOfO φ) ParkedCtxP.nil).toE
      (stabP par [negOfO φ] [] (negOfO φ) ParkedCtxP.nil).toA,
   hasUI_of_stabilisesP (todo := []) (done := []) s2 a2 ParkedCtxP.nil
      (stabP par [] [] (negOfO φ) ParkedCtxP.nil).toE
      (stabP par [] [] (negOfO φ) ParkedCtxP.nil).toA⟩

/-- **N5, as a theorem.**  A uniform-interpolant pair at EVERY generalised
station, from N4 at the saturated ones. -/
noncomputable def hasUI_of_stab {p : String} (s2 : SatE2P p) (a2 : SatA2P p)
    (par : StabilisationAllP p) (todo done : List Neg) (G : Neg)
    (hP : ParkedCtxP done) : HasUI p (todo ++ done) G :=
  hasUI_of_stabilisesP s2 a2 hP
    (stabP par todo done G hP).toE (stabP par todo done G hP).toA

/-- **N6 from N4 alone.**  Uniform interpolation for PLL follows from
stabilisation at the saturated parked stations, over the two cofinality
statements as variables:

    (∀ p, SatE2P p) → (∀ p, SatA2P p) → (∀ p, StabilisationAllP p) → PLL_UI
-/
noncomputable def pll_ui_of_stabilisationAll (s2 : ∀ p, SatE2P p)
    (a2 : ∀ p, SatA2P p) (par : ∀ p, StabilisationAllP p) : PLL_UI :=
  pll_ui_of_ljfo' (fun p => cellsFor_of_stab (s2 p) (a2 p) (par p))

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

/-! ## Pins (Stage 2)

Measured with `#axioms_within_pin`.  The transfer itself spends no more than
the composition principle does: the clause transporters and the focused step
are at `[propext, Quot.sound]`, and `Classical.choice` enters exactly through
`cutInv` — in `StabAt.raiseTo`, `stabP_of_stabilises` and the two `∀p` rows of
the branching clause, i.e. wherever two thresholds have to be merged. -/

#axioms_within LJFO.StabAt [propext]
#axioms_within LJFO.StabP [propext]
#axioms_within LJFO.StabAt.mk1 [propext, Quot.sound]
#axioms_within LJFO.StabP.toE [propext]
#axioms_within LJFO.StabP.toA [propext]
#axioms_within LJFO.cut1N [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.cut2N [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.cut2N' [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.swapInv2 [propext]
#axioms_within LJFO.StabAt.raiseTo [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.stabP_of_stabilises [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.StabP.step [propext, Quot.sound]
#axioms_within LJFO.stabP_fls [propext, Quot.sound]
#axioms_within LJFO.andAllImpUse [propext, Quot.sound]
#axioms_within LJFO.stabP_or_at [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.stabP_or [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.StabilisationAllP [propext]
#axioms_within LJFO.stabP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.cellsFor_of_stab [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hasUI_of_stab [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.pll_ui_of_stabilisationAll [propext, Classical.choice, Quot.sound]
