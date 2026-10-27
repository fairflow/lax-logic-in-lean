import LaxLogic.PLL.SemUI.SemUILayered
import Meta.Audit

/-!
# The sorried amalgamation lemma of `SemUILayered`, outside the library

Moved verbatim from `LaxLogic/PLL/SemUI/SemUILayered.lean` on 2026-10-27
(F0 re-implementation plan, decision D6, Matthew): the theorem carries a
`sorry`, so it is not trusted; no declaration used it; and its old module is in
the import closure of the subframe tableau
(`SubTab/Semantics` → `SubframeLayered` → `SemUIFrag` → `SemUILayered`).  The
name `PLLND.SemUI.amalgamation`, the statement and the docstring are unchanged.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-- **THE PLL AMALGAMATION LEMMA** (their Lemma 5.4 / Visser's Lemma
5.1; OPEN — the central open problem of the route, equivalent in
strength to the residues of the box-commutation law).

Given an adequate set X, a model K whose root k₀ is layered-bisimilar
to m₀ ∈ M at level 2·(nu X)+1 protecting everything but p, there is a
p-VARIANT of M (unbounded bisimulation!) whose root agrees with k₀ on
all of X.

Their proof shape to adapt: amalgam worlds = pairs ⟨Δ, m⟩ with Δ an
X-prime theory of the finite pre-Henkin model and m ∈ M, admissible
when a witnessing triple k′ ≼ k, k′ Z_{2d(k′)+1} m′, k Z_{2d(k′)} m
exists (d = Henkin depth of Δ); relations componentwise; atoms from
the union of the coordinates.  PLL additions needed: the fallibility
clauses (F-absorption as in `descGraft_force_iff`), the frame
conditions Rₘ ⊆ Rᵢ and reflexivity of Rₘ on the amalgam, and the
promise components of the canonical theories in the ◯-case (where
their ⊏-maximality trick, which uses irreflexivity/Löb, must be
replaced by idempotence-and-promise reasoning). -/
theorem amalgamation (X : Finset PLLFormula) (hX : SubClosed X)
    (p : String) (K M : ConstraintModel) (k₀ : K.W) (m₀ : M.W)
    (B : LayeredBisim (fun a => a ≠ p) K M)
    (hB : B.Z (2 * nu X + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ) := by
  sorry

/-! The `sorry` is deliberate and pinned at its site, as the experimental estate
asks (`Audit/Experimental.lean`). -/

#axioms_within amalgamation [propext, Classical.choice, Quot.sound, sorryAx]

end SemUI
end PLLND
