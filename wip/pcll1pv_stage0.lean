/-
STAGE 0 of `docs/pcll-1pv-ui-plan.md` — statements first, screens before
proofs.  Nothing here is proved except glue; every Prop is named so the
battery screens and the stage-1 proofs have fixed targets.

Reading that fixed these statements (2026-08-12): `witAmalgamC`'s `Ri`
and `Rm` are COMPONENTWISE on `(canonFinC cl).W × M.W` (restricted to
the triple subtype), so `amalgam_confluent` decomposes as
  (i)  confluence of `canonFinC cl`        [S1 screens it]
  (ii) confluence of `M`                   [free in the PCLL setting]
  (iii) a witnessing triple AT THE CORNER  [`CornerTriple`; S2 screens]
and (iii) is the only genuinely new maintenance obligation.  The other
open Prop of the route is pillar 3's `MforthResidue`, taken here in its
confluent form [S3 screens the §3 bare-possibility claim that it
trivialises].
-/
import wip.witTripleC

namespace PLLND
open FinComp
namespace SemUI

variable {p : String} {K M : ConstraintModel}

/-! ## The named obligations -/

/-- **The crux** (confluent-ui-plan, "the `amalgam_confluent` obligation
replaces the promise bookkeeping"): the amalgam lies in the confluent
class whenever both inputs do.  Required because the PCLL p-variant
must itself be a PCLL model. -/
def AmalgamConfluent (cl : Finset PLLFormula)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  MutuallyConfluent K → MutuallyConfluent M →
    MutuallyConfluent (witAmalgamC cl B)

/-- **The isolated content of the crux**: some componentwise confluence
corner carries a witnessing triple.  (Both component corners exist by
the component confluences; the subtype demands a triple at one of
them.) -/
def CornerTriple (cl : Finset PLLFormula)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  MutuallyConfluent K → MutuallyConfluent M →
  ∀ {a b c : (witAmalgamC cl B).W},
    (witAmalgamC cl B).Rm a b → (witAmalgamC cl B).Ri a c →
    ∃ (u₁ : (canonFinC cl).W) (u₂ : M.W),
      (canonFinC cl).Ri b.1.1 u₁ ∧ (canonFinC cl).Rm c.1.1 u₁ ∧
      M.Ri b.1.2 u₂ ∧ M.Rm c.1.2 u₂ ∧
      WitTripleC cl B u₁ u₂

/-- Glue: the crux follows from its isolated content. -/
theorem amalgamConfluent_of_corner {cl : Finset PLLFormula}
    {B : LayeredBisimWit (fun a => a ≠ p) K M}
    (h : CornerTriple cl B) : AmalgamConfluent cl B := by
  intro hK hM
  intro a b c hab hac
  obtain ⟨u₁, u₂, hbu₁, hcu₁, hbu₂, hcu₂, htrip⟩ := h hK hM hab hac
  exact ⟨⟨(u₁, u₂), htrip⟩, ⟨hbu₁, hbu₂⟩, ⟨hcu₁, hcu₂⟩⟩

/-- Pillar 3's residue, confluent form — the §3 claim is that under
bare possibility this holds because the promise-pair configuration
cannot arise. -/
def ConfResidue (cl : Finset PLLFormula)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  MutuallyConfluent M → MforthResidue cl B

/-- **The stage-3 target at the amalgamation interface**: the
assembled amalgamation strengthened by confluence of the p-variant.
Follows from `amalgamation_assembledC` + `AmalgamConfluent` (glue,
stage 1); the Thm 5.1 wrapper then instantiates `B` and discharges
`hres` via `ConfResidue`. -/
def OneVarConfluentAmalgamation (p : String) : Prop :=
  ∀ (K M : ConstraintModel) (cl : Finset PLLFormula),
    SubClosed cl → OBoxAdeq cl →
    MutuallyConfluent K → MutuallyConfluent M →
    ∀ (B : LayeredBisimWit (fun a => a ≠ p) K M),
      B.MBack → MforthResidue cl B →
      AmalgamConfluent cl B →
      ∀ (k₀ : K.W) (m₀ : M.W), B.Z (2 * cl.card + 1) k₀ m₀ →
        ∃ (N : ConstraintModel), MutuallyConfluent N ∧
          ∃ (C : PBisim p M N) (n₀ : N.W),
            C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ)

/-! ## The screens (specifications; implementations follow in this
stage before any stage-1 proof)

* **S1 (`canonFinC` confluence)**: for battery-derived ◯-adequate
  closures `cl`, check `MutuallyConfluent (canonFinC cl)` by direct
  enumeration of `WC cl` (finite; `Ri` is Finset inclusion, `Rm` is
  `RmC`).  A failure here refutes component (i) and redirects stage 1
  to repairing `RmC` before anything else.
* **S2 (`CornerTriple`, proxied)**: on p-pure confluent battery pairs
  `(K, M)` with a computable bounded-rank agreement link standing in
  for `B` (crank-bounded variable-free agreement, per
  `wip/stabilise.lean`'s `dict_agree_stab` interface — as a SCREEN
  only, no dictionary assumed), enumerate triple corners and check a
  triple exists at a componentwise corner.  The `top` escape
  (`⊥ ∈ val`, fallible partner) must be exercised by at least one
  cell (non-vacuity check, per the biint handoff's lesson).
* **S3 (`ConfResidue` vacuity)**: re-run the `bii_probe` residue
  configuration search RESTRICTED to mutually confluent `M` (the
  original battery allowed non-confluent `M`; 0/13,204 held even
  there, so the expectation is emptiness again — but the confluent
  run is the one this route consumes, and the d ≥ 3 open region
  deserves frames beyond the old battery's stabilisation depth). -/

end SemUI
end PLLND
