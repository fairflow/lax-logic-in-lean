/-
# The screen's certified verdicts

`wip/cutinv_screen.lean` runs a three-valued screen; a `fail` is only
ever issued on a certificate, and this file is where the two certificates
the screen found are made kernel theorems.

The mechanism is the ROUND TRIP of `LJF/OSearch.lean`: `LSeq.search` is
sound at every fuel (`search_sound`) and complete at fuel = derivation
height (`search_complete`).  So a sequent whose backward rule-instance
enumeration `succs` is EMPTY has no derivation at all — not merely none
below a budget.  Two families of `Inv` sequents are empty for that
reason, and both are LAX goals whose head connective has only a
truth-flagged right rule (`impR`, `andR` are `tru`-only, since at `lax`
they would assert the converse of K).

Consequence, stated below: the polarisation-invariance statement

    PolInv := ∀ Γ j ψ, Nonempty (LaxND (eraseCtx Γ) (goal j (eraseNeg ψ)))
                       → Nonempty (Inv Γ [] j ψ)

is **REFUTED**, at `Γ = []`, `j = lax`, `ψ = a ⊃ ↑a`.  And the refutation
does NOT carry to `CutInv`, because at such a `ψ` the SECOND premise of
`CutInv` is empty by the same lemma: the counterexample is vacuous for
cut.  Both facts are theorems here, so the report's claim that route (a)
must handle the lax flag separately rests on a kernel check and not on a
search verdict.
-/
import LJF.OSearch
import LJF.OBridge

namespace CutInvScreen

open LJFO PLLND

/-! ## 1. No rule instances ⟹ no derivation -/

/-- A sequent with no backward rule instance is unsearchable at every
fuel. -/
theorem search_false_of_succs_nil {s : LSeq} (h : LSeq.succs s = []) :
    ∀ n, LSeq.search n s = false := by
  intro n
  cases n with
  | zero => rfl
  | succ k => simp [LSeq.search, h]

/-- …hence, by completeness at fuel = height, underivable. -/
theorem isEmpty_of_succs_nil {s : LSeq} (h : LSeq.succs s = []) :
    IsEmpty s.holds :=
  ⟨fun d =>
    let ⟨n, hn⟩ := LSeq.search_complete d
    absurd hn (by rw [search_false_of_succs_nil h n]; exact Bool.noConfusion)⟩

/-! ## 2. The two empty families at the lax flag -/

theorem succs_inv_lax_imp_nil (Γ : List Neg) (Q : Pos) (N : Neg) :
    LSeq.succs (.inv Γ [] .lax (.imp Q N)) = [] := rfl

theorem succs_inv_lax_and_nil (Γ : List Neg) (M N : Neg) :
    LSeq.succs (.inv Γ [] .lax (.and M N)) = [] := rfl

/-- **An implication is never a lax goal.**  `impR` is truth-only, and no
`Ω`-rule applies at an empty pending zone, so the sequent `Γ ⊢lax Q ⊃ N`
has no rule instance at all. -/
theorem inv_lax_imp_empty (Γ : List Neg) (Q : Pos) (N : Neg) :
    IsEmpty (Inv Γ [] .lax (.imp Q N)) :=
  isEmpty_of_succs_nil (s := .inv Γ [] .lax (.imp Q N)) (succs_inv_lax_imp_nil Γ Q N)

/-- **A conjunction is never a lax goal**, for the same reason. -/
theorem inv_lax_and_empty (Γ : List Neg) (M N : Neg) :
    IsEmpty (Inv Γ [] .lax (.and M N)) :=
  isEmpty_of_succs_nil (s := .inv Γ [] .lax (.and M N)) (succs_inv_lax_and_nil Γ M N)

/-! ## 3. `PolInv` is REFUTED

The witness is the smallest one the screen produced: the empty context,
the lax flag, and the goal `a ⊃ ↑a`, whose erasure `◯(a ⊃ a)` is a PLL
theorem by `laxIntro` over the identity. -/

/-- The witness sequent's goal. -/
def wImpA : Neg := .imp (.atom "a") (.up (.atom "a"))

/-- The erased goal really is `◯(a ⊃ a)`. -/
theorem wImpA_erasure : goal .lax (eraseNeg wImpA) =
    PLLFormula.somehow (.ifThen (.prop "a") (.prop "a")) := rfl

/-- The erasure is PLL-provable, by a closed term. -/
def wImpA_provable : LaxND (eraseCtx []) (goal .lax (eraseNeg wImpA)) :=
  .laxIntro (.impIntro (.iden (List.mem_cons_self ..)))

/-- **`PolInv` is REFUTED.**  A polarised sequent whose erasure is
PLL-provable but which has no LJF◯ derivation: the hypothesis of
polarisation invariance holds and its conclusion is empty. -/
theorem polInv_refuted :
    Nonempty (LaxND (eraseCtx []) (goal .lax (eraseNeg wImpA))) ∧
      IsEmpty (Inv [] [] .lax wImpA) :=
  ⟨⟨wImpA_provable⟩, inv_lax_imp_empty [] (.atom "a") (.up (.atom "a"))⟩

/-! ## 4. …and the refutation is VACUOUS for `CutInv`

At a lax `⊃`- or `∧`-goal the second premise of `CutInv` is empty by the
very same lemma, so no instance of `CutInv` has both premises inhabited
there.  `CutInv` is therefore NOT refuted by `polInv_refuted`; the
`PolInv` route to it is. -/

theorem cutInv_premise2_empty_lax_imp (Δ : List Neg) (N : Neg) (Q : Pos) (M : Neg) :
    IsEmpty (Inv (N :: Δ) [] .lax (.imp Q M)) :=
  inv_lax_imp_empty (N :: Δ) Q M

theorem cutInv_premise2_empty_lax_and (Δ : List Neg) (N M₁ M₂ : Neg) :
    IsEmpty (Inv (N :: Δ) [] .lax (.and M₁ M₂)) :=
  inv_lax_and_empty (N :: Δ) M₁ M₂

/-- The conclusion is empty there too, so the `CutInv` instance at such a
`ψ` is an implication with an uninhabited antecedent AND an uninhabited
consequent: it holds trivially. -/
def cutInv_holds_vacuously_at_lax_imp (Γ Δ : List Neg) (N : Neg)
    (Q : Pos) (M : Neg) :
    Inv Γ [] .tru N → Inv (N :: Δ) [] .lax (.imp Q M) →
      Inv (Γ ++ Δ) [] .lax (.imp Q M) :=
  fun _ d => ((cutInv_premise2_empty_lax_imp Δ N Q M).false d).elim

def cutInv_holds_vacuously_at_lax_and (Γ Δ : List Neg) (N M₁ M₂ : Neg) :
    Inv Γ [] .tru N → Inv (N :: Δ) [] .lax (.and M₁ M₂) →
      Inv (Γ ++ Δ) [] .lax (.and M₁ M₂) :=
  fun _ d => ((cutInv_premise2_empty_lax_and Δ N M₁ M₂).false d).elim

/-! ## 5. Pins (measured below) -/

#print axioms isEmpty_of_succs_nil
#print axioms inv_lax_imp_empty
#print axioms inv_lax_and_empty
#print axioms wImpA_provable
#print axioms polInv_refuted
#print axioms cutInv_holds_vacuously_at_lax_imp

end CutInvScreen
