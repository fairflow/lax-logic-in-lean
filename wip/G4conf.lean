import LaxLogic.PLLConfluentComplete
import LaxLogic.PLLG4H

/-!
# G4cf — a cut-free sequent calculus for CONFLUENT PLL

Branch `ui-confluence`.  Design in `docs/confluent-ui-plan.md`.

`G4cf` = the repaired complete calculus `G4c` (`PLLG4H.lean`, the
height-indexed `G4h`) PLUS one additive left rule `distL` for the
distribution scheme `◯(A∨B) ⊃ (◯A∨◯B)`, which is sound and complete for
mutually confluent constraint models (`PLLFrames.lean:224`,
`PLLConfluentComplete.lean`).  On such models the ∀∃-clause for ◯
collapses to bare possibility `w ⊩ ◯φ ↔ ∃u, Rₘ w u ∧ u ⊩ φ`.

The 17 `G4h` rules are copied verbatim (a `G4h → G4hf` rename); `distL`
is the one new rule.  Every ported metatheorem gets exactly one new case.

Proved here: `force_dist_elim` (the semantic core of `distL`-soundness).
Stated with precise port-comments (Matthew's licence to assume the
heavier metatheory for now): full soundness, completeness via `DerivU`,
cut admissibility, and the `G4c ⊆ G4cf` embedding.
-/

open PLLFormula

namespace PLLND
namespace G4Conf

/-- **G4cf, height-indexed.**  The 17 rules of `G4h` (`PLLG4H.lean:49`)
verbatim, plus `distL`.  Premises at `n`, conclusion at `n+1`. -/
inductive G4hf : Nat → List PLLFormula → PLLFormula → Prop
  | init {n : Nat} {Γ : List PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4hf n Γ (prop a)
  | botL {n : Nat} {Γ : List PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4hf n Γ C
  | andR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n Γ A → G4hf n Γ B → G4hf (n + 1) Γ (A.and B)
  | orR1 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n Γ A → G4hf (n + 1) Γ (A.or B)
  | orR2 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n Γ B → G4hf (n + 1) Γ (A.or B)
  | impR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n (A :: Γ) B → G4hf (n + 1) Γ (A.ifThen B)
  | laxR {n : Nat} {Γ : List PLLFormula} {A : PLLFormula} :
      G4hf n Γ A → G4hf (n + 1) Γ A.somehow
  | andL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.and B :: Δ)) :
      G4hf n (A :: B :: Δ) C → G4hf (n + 1) Γ C
  | orL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.or B :: Δ)) :
      G4hf n (A :: Δ) C → G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  | laxL {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula}
      (h : A.somehow ∈ Γ) :
      G4hf n (A :: Γ) B.somehow → G4hf (n + 1) Γ B.somehow
  | impLProp {n : Nat} {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ) :
      G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  | impLBot {n : Nat} {Γ Δ : List PLLFormula} {B C : PLLFormula}
      (h : Γ.Perm (falsePLL.ifThen B :: Δ)) :
      G4hf n Δ C → G4hf (n + 1) Γ C
  | impLAnd {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.and B).ifThen D :: Δ)) :
      G4hf n (A.ifThen (B.ifThen D) :: Δ) E → G4hf (n + 1) Γ E
  | impLOr {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.or B).ifThen D :: Δ)) :
      G4hf n (A.ifThen D :: B.ifThen D :: Δ) E → G4hf (n + 1) Γ E
  | impLImp {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
      G4hf n (B.ifThen D :: Δ) (A.ifThen B) → G4hf n (D :: Δ) E →
      G4hf (n + 1) Γ E
  | impLLax {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4hf n Γ A → G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  | impLLaxLax {n : Nat} {Γ Δ : List PLLFormula} {A B X C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) (hX : X.somehow ∈ Δ) :
      G4hf n (X :: Γ) A.somehow → G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  -- the one new rule: ◯∨-distribution as an analytic left rule
  | distL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm ((A.or B).somehow :: Δ)) :
      G4hf n (A.somehow :: Δ) C → G4hf n (B.somehow :: Δ) C →
      G4hf (n + 1) Γ C

/-- The working judgment: derivable in confluent PLL at some height. -/
def G4cf (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4hf n Γ C

/-! ## The semantic core of `distL`-soundness (PROVED)

On mutually confluent models `◯(A∨B)` gives `◯A ∨ ◯B` — the exact fact
the new rule needs, a two-line corollary of the already-proven
`force_somehow_or_dist_of_confluent` (`PLLFrames.lean:240`). -/

theorem force_dist_elim {M : ConstraintModel} (hc : MutuallyConfluent M)
    {w : M.W} {A B : PLLFormula} (h : M.force w (somehow (A.or B))) :
    M.force w (somehow A) ∨ M.force w (somehow B) := by
  have hd := force_somehow_or_dist_of_confluent hc w A B
  have hor := hd w (M.refl_i w) h
  simpa [ConstraintModel.force] using hor

/-! ## Metatheory (soundness proved for the new rule; the ported bulk
stated with precise obligations, per the standing licence to assume). -/

/-- **Soundness for confluent models.**  PORT: induction on `G4hf`; the
17 `G4h` cases mirror the existing G4c soundness verbatim, and the sole
new case `distL` is discharged by `force_dist_elim` together with a case
split on the resulting `◯A ∨ ◯B`.  Stated now; the shared-case bulk is
the mechanical port. -/
theorem G4cf_sound {Γ : List PLLFormula} {C : PLLFormula} (d : G4cf Γ C)
    {M : ConstraintModel} (hc : MutuallyConfluent M) {w : M.W}
    (hΓ : ∀ φ ∈ Γ, M.force w φ) : M.force w C := by
  sorry

/-- **`G4cf` extends `G4c`.**  Every `G4h` rule is a `G4hf` rule, so the
embedding is a 17-case rename induction (no new mathematics). -/
theorem G4cf_of_G4c {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4c Γ C) : G4cf Γ C := by
  sorry

/-- **`G4cf` derives every distribution instance.**  From `◯A ⊢ ◯A∨◯B`
and `◯B ⊢ ◯A∨◯B` by `distL` — the completeness bridge to `DerivU`.
(Quick once `orR`/`init`-for-`◯` plumbing is in; stated for now.) -/
theorem G4cf_distF (A B : PLLFormula) :
    G4cf [] ((somehow (A.or B)).ifThen ((somehow A).or (somehow B))) := by
  sorry

/-- **Completeness for confluent models**, via `DerivU`
(`derivU_iff_confluent_valid`, `PLLConfluentComplete.lean`): `G4cf` and
`DerivU` derive the same sequents (`G4cf_of_G4c` + `G4cf_distF` one way;
soundness the other), and `DerivU` is complete for the confluent class. -/
theorem G4cf_complete {Γ : List PLLFormula} {C : PLLFormula}
    (hv : ∀ (M : ConstraintModel), MutuallyConfluent M → ∀ w : M.W,
      (∀ φ ∈ Γ, M.force w φ) → M.force w C) : G4cf Γ C := by
  sorry

/-- **Cut admissibility for `G4cf`.**  ASSUMED (Matthew's licence).
Later: port `PLLG4HCut` — the 17 shared cases verbatim, plus the
`distL`/cut interaction (standard: cut permutes above `distL` into both
branches, the cut formula strictly smaller or the height dropping). -/
theorem G4cf_cut {Γ : List PLLFormula} {A C : PLLFormula}
    (d₁ : G4cf Γ A) (d₂ : G4cf (A :: Γ) C) : G4cf Γ C := by
  sorry

end G4Conf
end PLLND
