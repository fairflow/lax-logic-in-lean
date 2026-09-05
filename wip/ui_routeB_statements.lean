/-
Route (B) — the four statements, as TYPED DEFINITIONS (the `CimpAnt`
idiom: a `def … : Type`, never a sorried theorem, so nothing is asserted).
Drafted 2026-09-04 to be surfaced before any proof is built.

`interpF` (`LJF/OFuel.lean`) is the fuel-founded retaining interpolant.
Every fuel level is sound by construction; the two soundness statements
mirror `eSound`/`aSound` with a fuel argument and are expected to be
mechanical ports.  The two minimality statements are the plan's
"cofinality": a sufficient `p`-free formula sits below the interpolant
taken at the HEIGHT of its own derivation, so that the fuel needed is
finite and computable from the derivation, not from the station — hence
`Σ`, not `∃`: the fuel is DATA (the plan's `A_{height of θ's derivation}`).
-/
import LJF.O
import LJF.OFuel
import LJF.OFuelSound
import LJF.OFuelMin
import LJF.OFuelP
import LJF.OFuelPSound
import LJF.OFuelPMin
import LJF.OFuelPCof

namespace LJFO

/-- E1 at every fuel: the station derives its own ∃p-approximant. -/
def ESoundF (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpF p f todo done none)

/-- A1 at every fuel: the ∀p-approximant beside the station derives the goal. -/
def ASoundF (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G

/-! Both soundness statements are INHABITED (`LJF/OFuelSound.lean`,
2026-09-04), each `[propext, Quot.sound]`. -/

/-- `ESoundF` holds. -/
def esoundF (p : String) : ESoundF p := eSoundF p

/-- `ASoundF` holds. -/
def asoundF (p : String) : ASoundF p := aSoundF p

/-- Cofinality, ∃ side: a `p`-free consequence of a saturated station is a
consequence of the approximant at the derivation's height. -/
def ECofinalF (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ),
      Σ f : Nat, Inv (interpF p f [] done none :: Δ) [] j ψ

/-- Cofinality, ∀ side: a `p`-free hypothesis sufficient for the goal sits
below the approximant at some finite fuel (E-relativised, as `SatA2`). -/
def ACofinalF (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j G),
      Σ f : Nat, Inv (interpF p f [] done none :: Δ) [] .tru
        (interpF p f [] done (some (jGoal j G)))

/-! ## Status of the two cofinality statements (2026-09-04)

Both are OPEN: neither is inhabited, and per the machine-checked mandate
neither gets a sorried declaration.  What IS proved sits in
`LJF/OFuelMin.lean`:

* the row layer of `interpF` at fuel `f+1` (the nine aggregate equations
  and the nine row memberships), all `[propext]`;
* `SatE2F` / `SatA2F`, the same two statements at a SATURATED station in
  upward-closed fuel form (`UpFrom` / `UpFrom2`), from which
  `ECofinalF` / `ACofinalF` follow by the projections below;
* `eMinFF` / `aMinFF`: the processing phase, unconditionally — cofinality
  at a saturated station implies cofinality at every station;
* `CimpAntF`, the isolated obligation of the twelve retention rows, and
  `cimpAntF_of_satA2F : SatA2F p → CimpAntF p` — the obligation is an
  instance of `SatA2F` itself, at the SAME station, applied to the
  antecedent's own subderivation.  That last is the content of the
  retention design and the reason it cannot simply be taken as a
  recursive call: see the termination note in `LJF/OFuelMin.lean`. -/

/-- `ECofinalF` follows from cofinality at a saturated station: read the
upward-closed witness at its own threshold. -/
def ecofinalF_of_satE2F {p : String} (s2 : SatE2F p) : ECofinalF p :=
  fun done Δ ψ hsat hP hΔ hψ _ d =>
    let w := s2 done Δ ψ hsat hP hΔ hψ d
    ⟨w.1, w.here⟩

/-- `ACofinalF` follows likewise, on the diagonal of the two fuels. -/
def acofinalF_of_satA2F {p : String} (a2 : SatA2F p) : ACofinalF p :=
  fun done Δ G hsat hP hΔ _ d =>
    let w := a2 done Δ G hsat hP hΔ d
    ⟨w.1, w.here⟩

/-! ## The same four statements for the PARKING interpolant `interpP`

`interpP` (`LJF/OFuelP.lean`, node N0e) is `interpF` with the three
reshaping processing clauses replaced by PARKING clauses, a row for each
newly parked shape, and the Dyckhoff rows' guard retained at the full
station.  The statements are the same, with `interpP` for `interpF` and
the extended parked-shape invariant `ParkedCtxP` for `ParkedCtx`. -/

/-- E1 at every fuel, for `interpP`. -/
def ESoundP (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpP p f todo done none)

/-- A1 at every fuel, for `interpP`. -/
def ASoundP (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpP p f todo done (some G) :: (todo ++ done)) [] .tru G

/-! Both are INHABITED (`LJF/OFuelPSound.lean`, 2026-09-05), each
`[propext, Quot.sound]` — the same measured set as the `interpF` pair. -/

/-- `ESoundP` holds. -/
def esoundP (p : String) : ESoundP p := eSoundP p

/-- `ASoundP` holds. -/
def asoundP (p : String) : ASoundP p := aSoundP p

/-- Cofinality, ∃ side, for `interpP`. -/
def ECofinalP (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j ψ),
      Σ f : Nat, Inv (interpP p f [] done none :: Δ) [] j ψ

/-- Cofinality, ∀ side, for `interpP` (E-relativised, as `ACofinalF`). -/
def ACofinalP (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtxP done →
    PFreeCtx p Δ →
    ∀ {j : JD} (d : Inv (done ++ Δ) [] j G),
      Σ f : Nat, Inv (interpP p f [] done none :: Δ) [] .tru
        (interpP p f [] done (some (jGoal j G)))

/-- `ECofinalP` follows from cofinality at a saturated station. -/
def ecofinalP_of_satE2P {p : String} (s2 : SatE2P p) : ECofinalP p :=
  fun done Δ ψ hsat hP hΔ hψ _ d =>
    let w := s2 done Δ ψ hsat hP hΔ hψ d
    ⟨w.1, w.here⟩

/-- `ACofinalP` follows likewise, on the diagonal of the two fuels. -/
def acofinalP_of_satA2P {p : String} (a2 : SatA2P p) : ACofinalP p :=
  fun done Δ G hsat hP hΔ _ d =>
    let w := a2 done Δ G hsat hP hΔ d
    ⟨w.1, w.here⟩

/-! The whole chain, from the two typed entry points of the cofinality
family (`LJF/OFuelPCof.lean`) down to the approved statements.  Only the
top link is open. -/

/-- `ECofinalP` from the `∃p` traversal. -/
def ecofinalP_of_tinvP {p : String} (t : TInvP p) : ECofinalP p :=
  ecofinalP_of_satE2P (satE2P_of_tinvP t)

/-- `ACofinalP` from the `∀p` entry. -/
def acofinalP_of_uentryP {p : String} (u : UEntryP p) : ACofinalP p :=
  acofinalP_of_satA2P (satA2P_of_uentryP u)

end LJFO

#axioms_within LJFO.ecofinalF_of_satE2F [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.acofinalF_of_satA2F [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.esoundP [propext, Quot.sound]
#axioms_within LJFO.asoundP [propext, Quot.sound]
#axioms_within LJFO.ecofinalP_of_satE2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.acofinalP_of_satA2P [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.ecofinalP_of_tinvP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.acofinalP_of_uentryP [propext, Classical.choice, Quot.sound]
