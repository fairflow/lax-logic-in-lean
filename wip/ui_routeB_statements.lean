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

namespace LJFO

/-- E1 at every fuel: the station derives its own ∃p-approximant. -/
def ESoundF (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpF p f todo done none)

/-- A1 at every fuel: the ∀p-approximant beside the station derives the goal. -/
def ASoundF (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G

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

end LJFO
